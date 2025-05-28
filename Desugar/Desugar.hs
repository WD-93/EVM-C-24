{-# LANGUAGE LambdaCase #-}
module Desugar.Desugar where
--A separate module for desugaring; Compiler should just tie each stage
--together and handle the IO.

import Util (complainIf)
--import E.Par (pM,myLexer)
--import E.ErrM (Err(..))
import E.Abs (Ident(..),UIdent(..))
import qualified E.Abs as P

--CST -> AST
import AST.DTs
--AST -> AST

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)
import Data.Char (ord) --for string desugaring
import Control.Arrow ((***))
import Data.Maybe (fromMaybe)

data DError = DuplicateDefun Name
            | BadDOrdering [P.D]
            | BadOpInType String
            | BadEInType P.E --catch-all error for desugarT
            | BadEInPat P.E --same for desugarP
            | BadDoInDesugarS [P.S]
            | AssignIsNotAnE P.E P.E --for now
            | DuplicateDeclsForName Name
            -- | CoerceMixedWithOps [Name]
            | GenericDError String
            -- | BitPaddingDeprecated
            --TODO remove bit padding from syntax and compiler
            | NegativeLengthArray Name Integer
            | TooLongArray Name Integer
            | StandaloneConstructorName String
            | DuplicateConstructors Name
            | BadPatternInCase P.E
            | MoreThan256EnumNamesInOneEnum
            -- ^A helpful message on the off chance whoever triggers it isn't
            --fuzzing for vulns
            | DuplicateEnumName Name Name
            | WildcardInExprContext
            | MalformedPattern P.E
            | DuplicateTySigs Name
            | DuplicateKindSigs Name
            | UnresolvedImport P.ModuleName
            | DuplicateTyCons Name
            | NonByteChar String
            | DuplicateFieldNames Name
  deriving (Eq,Ord,Read,Show)

--Declarations are order-independent, modulo the static names allocated to
--strings (which should be irrelevant to compilation if it's successful).
desugar :: P.M -> Either DError Module
desugar (P.Module ds) =
  case runState (runExceptT $ mapM_ desugarD ds) emptyModule of
    (Left derr, _) -> Left derr
    (Right (), m) -> Right m
emptyModule =
  Module {
  tysigs = M.empty,
  kindsigs = M.empty,
  sorts = S.empty,
  defuns = M.empty,
  tysyns = M.empty,
  static = M.empty,
  globals = M.empty,
  datatypes = M.empty,
  datatypeRegions = M.empty,
  constructors = M.empty,
  fieldTypes = M.empty,
  fieldSpecs = M.empty,
  anonStaticCtr = 0
  }

type De = ExceptT DError (State Module)

desugarD :: P.D -> De ()
desugarD = \case
  P.Defun (Ident f) lhs ps -> do
    checkForDuplicates f
    --Note patterns are a subset of syntactically valid Es
    p <- desugarP lhs
    --Need to add do block support to DTs?
    s <- desugarS ps
    modify (\m->m{defuns=M.insert f (p,s) $ defuns m})
  P.TySig (Ident f) pt ->
    addSig f pt tysigs (\x m -> m{tysigs=x}) DuplicateTySigs
  --Now tycons can either be level 1 (a la Memory, Word)
  --or level 2 (a la Region, Type).
  --Top-level kinds (level 2) can only be declared as Tycon : Kind
  --While they could in theory live in different namespaces, we instead check
  --that level-1 tycons don't collide with level-2 and vice versa.
  P.KindSig (UIdent tycon) pk -> do
    let k = desugarT pk
    ksigs <- gets kindsigs
    srts <- gets sorts
    --TODO add more informative error message
    complainIf (S.member tycon $ S.union srts $ M.keysSet ksigs)
      $ DuplicateKindSigs tycon
    if k == TyCon "Kind"
      then modify(\m->m{sorts = S.insert tycon srts})
      else modify(\m->m{kindsigs = M.insert tycon k ksigs})
  P.TySyn conargs te -> do
    let (nm,args) = desugarConArgs conargs
    let t = desugarT te
    modify (\m -> m{tysyns = M.insert nm (args,t) $ tysyns m})
  P.Import mnm -> throwE $ UnresolvedImport mnm
  --Decision: fixed-size arrays are now a first-class type; array globals no
  --longer decay to pointers.
  --arr[len > 65536] needn't be caught... it's fine if it's an array of ()!
  P.Global pr varBind -> do
    (x,me) <- desugarVarBind varBind
    checkForDuplicates x
    let r = read $ take 2 $ show pr
    modify (\m->m{globals = M.insert x (r,me) $ globals m})
  --Relevant:
  --datatypes: params, conDecls
  --datatypeRegions: if Just r <- mr insert it
  --constructors: con : arg1 -> arg2 -> ... -> tycon params
  --fieldTypes: tycon params -> argN
  --fieldSpecs: con, n
  P.Data conArgs dataRHS -> do
    let (tycon,args) = desugarConArgs conArgs
        (condecls,mr) = desugarDataRHS dataRHS
    checkForDupTyCon tycon
    --Insert datatype entry
    modify (\m->m{datatypes = M.insert tycon (args,condecls) $
                 datatypes m})
    --If Just r <- mr insert it
    case mr of
      Just r -> modify (\m->m{datatypeRegions = M.insert tycon r $
                               datatypeRegions m})
      Nothing -> return ()
    --Add type signatures for constructors
    --TODO move them to tysigs instead? Need to check they're not underapplied,
    --so they should be treated differently. But for that I only need arity...
    let rett :: T --the return type of constructors
        rett = foldl (:$$) (TyCon tycon) $ map TyVar args
    let conArgs :: [(Name,[T])]
        conArgs = map (id *** (\case Left ts -> ts; Right nmts -> map snd nmts))
                  condecls
        conTs :: [(Name,T)]
        conTs = map (id *** (foldr (:->) rett)) conArgs
    mapM_ (\(con,t) -> do
              checkForDuplicates con
              modify (\m->m{constructors=M.insert con t $ constructors m}))
      conTs
    --Insert field types
    let conFields :: [(Name,Name,Int,T)] --(con,field nm,index,field type)
        conFields = do
          (con,ei) <- condecls
          case ei of
            Left _ -> [] --no fields
            Right nmts -> do
              (ix,(nm,t)) <- zip [0..] nmts
              return (con,'.':nm,ix,t)
    mapM_ (\(con,nm,ix,t) -> do
              s <- get
              let fts = fieldTypes s
              complainIf (M.member nm fts)
                $ DuplicateFieldNames nm
              put s{fieldTypes = M.insert nm (rett :-> t) fts,
                    fieldSpecs = M.insert nm (con,ix) $ fieldSpecs s}
          )
      conFields
  P.StaticData (Ident nm) pe -> do
    checkForDuplicates nm
    e <- desugarE pe
    modify (\m->m{static=M.insert nm e $ static m})
    

desugarDataRHS :: P.DataRHS -> ([ConDecl],Maybe Name)
desugarDataRHS = \case
  P.Unboxed urhs ->
    let cons = desugarUnboxedRHS urhs
    in (cons,Nothing)
  P.Boxed urhs (Ident r) ->
    let cons = desugarUnboxedRHS urhs
    in (cons, Just r)
desugarUnboxedRHS :: P.UnboxedRHS -> [ConDecl]
desugarUnboxedRHS (P.URHS dcs) = map desugarDataCon dcs
desugarDataCon :: P.DataCon -> ConDecl
desugarDataCon = \case
  P.DCArgs dca ->
    let (con,ts) = desugarDCA dca
    in (con, Left ts)
  P.DCRecord (UIdent con) rfs ->
    let nmts = map desugarRecordField rfs
    in (con, Right nmts)
desugarDCA :: P.DCA -> (Name,[T])
desugarDCA = \case
  P.DCANil (UIdent con) -> (con,[])
  P.DCACons dca pt ->
    let t = desugarT pt
        (con,ts) = desugarDCA dca
    in (con,ts ++ [t])
desugarRecordField :: P.RecordField -> (Name,T)
desugarRecordField (P.RF (Ident nm) pt) = (nm,desugarT pt)

addSig :: Name -> P.T ->
          (Module -> Map Name T) ->
          (Map Name T -> Module -> Module) ->
          (Name -> DError) ->
          De ()
addSig nm pt getField setField err = do
    let t = desugarT pt
    map <- gets getField
    complainIf (M.member nm map)
      $ err nm
    modify $ setField $ M.insert nm t map
{-
  P.Data lhs rhs -> do
  --Duplicate params, duplicate constructors and free tyvars in arg types to
  --be caught in IR1
  --It's also not necessary to check params don't shadow non-type names;
  --they live in different namespaces.
  let (tycon,params) = desugarConLHS lhs
  conmts <- desugarConRHS (tycon,params) rhs
  checkForDuplicates tycon
  --We don't actually need to prevent collisions between constructors in
  --different datatypes, or between constructors and tysyns!
  --That's because the alloc ptr var gives you all the type info you need
  --on construction,
  --and e gives you a monomorphic type in case e of {...}.
  s <- get
  put s{datatypes = M.insert tycon (params,conmts) $ datatypes s}
  desugarDs rest
--Enums are currently 8b by default and have values 0..|ecs|-1.
--Ways enum can fail:
--tycon or member collision with existing value;
--duplicate member names;
-- >256 constructors
desugarDs ((P.Enum (UIdent tycon) ecs):rest) = do
  let nms = map (\(P.EC (Ident nm)) -> nm) ecs
  if length nms > 256
    then throwE MoreThan256EnumNamesInOneEnum
    else return ()
  case filter ((>1) . snd) $ count nms of
    (nm,_):_ -> throwE $ DuplicateEnumName tycon nm
    _ -> return ()
  checkForDuplicates tycon
  mapM_ checkForDuplicates nms
  s <- get
  put s{enums = M.insert tycon nms $ enums s,
        enumValues = M.union (M.fromList [(nm,(tycon,i))
                                         | (nm,i) <- zip nms [0..]])
                     $ enumValues s
       }
  desugarDs rest
desugarDs (P.StaticData pt (Ident nm) pe : rest) = do
  let t = desugarT pt
  e <- desugarE pe
  handleStaticData t nm e
  desugarDs rest
desugarDs (P.StaticDatatype pt (Ident nm) pe : rest) = do
  let t = desugarT pt
  e <- desugarE pe
  handleStaticDatatype t nm e
  desugarDs rest
desugarDs other = throwE $ BadDOrdering other
-}

count :: Ord a => [a] -> [(a,Int)]
count as =
  case sort as of
    [] -> []
    a:as' -> go a 1 as'
      where go a n = \case
              [] -> [(a,n)]
              a':as
                | a == a' -> go a (n+1) as
                | let -> (a,n) : go a' 1 as

--This can't fail, so there's no need to make it a monad
desugarConArgs :: P.ConArgs -> (Name,[Name])
desugarConArgs = go
  where go = \case
          P.CANil (UIdent tycon) -> (tycon,[])
          P.CACons conlhs (Ident param) ->
            let (tycon,params) = go conlhs
            in (tycon,params++[param]) --I know it's quadratic...

--This can fail because I use E for the constructors; todo make the BNFC
--syntax more restrictive so I don't need a bunch of unnecessary parentheses
--to get it to parse right...
--Now takes (tycon,params) in order to add each con to constructors with its
--type.
--TODO change to (Name,Name,[Name]) to reflect the fact that the param list
--will always be nonempty.
--Problem: I'm determining the tags in the desugaring phase!
--Maybe I should instead refer to a scheme for determining them, to be
--resolved in IR.
{-
desugarConRHS :: (Name,[Name]) -> [P.DataCon] -> De [(Name,T)]
desugarConRHS (tycon,r:params) cons =
  mapM (\(tag,(P.DC (UIdent con) parg)) -> do
           let arg = desugarT parg
           addConstructor con (tag,arg,tycon,r,params)
           return (con,arg)
       ) $ zip [0..] cons
-}

--Adds the info of a new constructor to the constructors map; throws an error
--if there's a duplicate. Constructors do not conflict with tysyns or tycons.
addConstructor :: Name -> T -> De ()
addConstructor con t = do
  checkForDuplicates con
  error "todo"

--The check for duplicate names for dynamic values; datatypes and tysyns have
--their own namespace.
--Potential opt: split check for lowercase names and constructors
checkForDuplicates :: Name -> De ()
checkForDuplicates nm = do
  m <- get
  --TODO give a more informative error message
  complainIf (S.member nm $ S.unions $
              [M.keysSet $ defuns m,
               M.keysSet $ static m,
               M.keysSet $ globals m,
               M.keysSet $ constructors m
              ])
    $ DuplicateDeclsForName nm
--Kind signatures render hardcoded prim tycons unnecessary!
--But they also mean datatypes may be mentioned twice: once in a kind
--signature and once in a data decl.
--So when desugaring a kind signature, one must check the kind signature map
--but not this function.
checkForDupTyCon :: Name -> De ()
checkForDupTyCon nm = do
  m <- get
  complainIf (S.member nm $ S.unions $
              [M.keysSet $ tysyns m,
               M.keysSet $ datatypes m
              ])
    $ DuplicateTyCons nm

desugarT :: P.T -> T
desugarT = go
  where go = \case
          P.TVar (Ident nm) -> TyVar nm
          P.TNat n -> TyNat n
          P.TCon (UIdent nm) -> TyCon nm
          P.TEmptyTup -> TyCon "Unit"
          P.TTup t ts -> tupleT $ map go $ t:ts
          P.TApp tf tx -> go tf :$$ go tx
          P.TArray len a -> Array (go len) (go a)
          P.TArrow a b -> go a :-> go b
{-
--The syntax ensures ordering: [wordpad] [wordalign] (fnm: t | t)
desugarFieldT :: P.TField -> Field T
desugarFieldT = go1
  where go1 = \case
          P.TPad fld -> go2 Word fld
          P.TF1 fld -> go2 Byte fld
        go2 pad = \case
          P.TAlign fld -> go3 pad Word fld
          P.TF2 fld -> go3 pad Byte fld
        go3 pad al = \case
          P.TNamed (Ident nm) pt ->
            ((pad,al),Just nm,desugarT pt)
          P.TAnon pt ->
            ((pad,al),Nothing,desugarT pt)
-}
{-
_, x, {p | field:p,...}, (p1,p2,...), *e, e[e], p.field, p#ix
In future: Con p
-}
desugarP :: P.E -> De Pat
desugarP = desugarE
{-
desugarP = go
  where go = \case
          P.EmptyTuple -> return $ PCon "Unit" []
          P.Tuple p ps ->
            foldr (\p1 p2 -> PCon "Pair" [p1,p2]) (PCon "Unit" [])
            <$> mapM go (p:ps)
          P.Var (Ident nm) -> return $ PVar nm
          P.Wild -> return PWild
          P.Index arr ix -> PIndex <$> desugarE arr <*> desugarE ix
          P.Dot p (Ident nm) -> (:.) <$> go p <*> return nm
          P.Deref e -> Deref <$> desugarE e
          e -> throwE $ MalformedPattern e
        todo = error "todo"
-}
{-
--Fields in patterns should never contain pad or align pragmas, so they cause
--an error
desugarFieldP :: P.EField -> De (Maybe Name, Pat)
desugarFieldP (P.EF1 (P.EF2 f)) =
  case f of
    P.ENamed (Ident nm) e -> do
      p <- desugarP e
      return (Just nm, p)
    P.EAnon e -> do
      p <- desugarP e
      return (Nothing, p)
    f -> throwE $ MalformedPatternField f
-}

desugarS :: P.S -> De S
desugarS = \case
  P.SE e -> SE <$> desugarE e
  P.If e th el -> Ifte <$> desugarE e <*> desugarS th <*> desugarS el
  P.While e body -> While <$> desugarE e <*> desugarS body
  P.Return e -> Return <$> desugarE e
  P.Do ss -> Block <$> mapM desugarS ss
  P.Case pe pcases -> do
    e <- desugarE pe
    cases <- mapM desugarCase pcases
    return $ Case e cases
  P.Break -> return Break
  P.Continue -> return Continue
  --for (start;cond;each) s => {start;while (cond) {s;each}}
  P.For {} -> error "todo for loops"
  P.Declare varBinds ->
    Declare <$> mapM (((id *** fromMaybe (Var "null" :$ Var "Unit"))<$>) .
                      desugarVarBind) varBinds

desugarVarBind :: P.VarBind -> De (Name, Maybe E)
desugarVarBind = \case
  P.JustVar (Ident nm) -> return (nm, Nothing)
  P.VarIs (Ident nm) pe -> ((,)nm) <$> Just <$> desugarE pe

--TODO allow _, x patterns in case
desugarCase :: P.CASE -> De (Pat,S)
desugarCase (P.C pe ps) = do
  p <- desugarP pe
  s <- desugarS ps
  return (p,s)

--desugarE needs to be in De because strings are translated to
--(&sv :: Ptr Code Byte[len]), where sv := a fixed-size byte array
desugarE :: P.E -> De E
desugarE = go
  where go = \case
          P.EmptyTuple -> return $ Var "Unit"
          P.Tuple pe pes -> tupleE <$> mapM go (pe:pes)
          --Integers are sugar for fromWord #w, where w is :: Word;
          --all overloading is implemented via function application under the
          --hood.
          P.HexInt (P.HexInteger str) -> go $ P.Int $ read str
          P.Int n -> return $ po1 "fromWord" $ EInteger n
          P.Var (Ident nm) -> return $ Var nm
          P.String str -> handleString str
          P.Con (UIdent nm) -> return $ Var nm
          --Patterns are now exprs...
          P.Wild -> return $ Var "_"
          --Without block exprs this becomes ugly...
          P.PlusPlusPost pe -> do
            e <- go pe
            return $ po2 "minus" (e := (po2 "plus" e (EInteger 1))) (EInteger 1)
          P.MinusMinusPost pe -> do
            e <- go pe
            return $ po2 "plus" (e := (po2 "minus" e (EInteger 1))) (EInteger 1)
          P.Index a b -> op2 "index" a b
          P.Dot e (Ident nm) -> op1 ('.' : nm) e
          P.Arrow pe (Ident nm) -> do
            e <- go pe
            return $ po1 ('.':nm) $ po1 "deref" e
          --I use array (e1,e2,...) as hacky syntax for array exprs
          P.App (P.Var (Ident "array")) ptup -> do
            tup <- go ptup
            case unTupleE tup of
              Just es -> return $ EArray es
              Nothing ->
                throwE $ GenericDError "Non-tuple passed to array 'function'"
          P.App pf px -> (:$) <$> go pf <*> go px
          P.PlusPlusPre pe -> do
            e <- go pe
            return $ e := (po2 "plus" e $ EInteger 1)
          P.MinusMinusPre pe -> do
            e <- go pe
            return $ e := (po2 "minus" e $ EInteger 1)
          P.Negate a -> op1 "negate" a
          P.Not a -> op1 "lNot" a
          P.BitwiseNot a -> op1 "bwNot" a
          P.Deref a -> op1 "deref" a
          P.AddressOf a -> op1 "ampersand" a
          P.Mul a b -> op2 "multiply" a b
          P.Div a b -> op2 "divide" a b
          P.Mod a b -> op2 "modulo" a b
          P.Plus a b -> op2 "plus" a b
          P.Minus a b -> op2 "minus" a b
          P.Shl a b -> op2 "shL" a b
          P.Shr a b -> op2 "shR" a b
          P.MyLT a b -> op2 "lt_" a b
          P.LTE a b -> op2 "lte_" a b
          P.MyGT a b -> op2 "gt_" a b
          P.GTE a b -> op2 "gte_" a b
          P.Eq a b -> op2 "eq_" a b
          P.NEq a b -> op2 "neq_" a b
          P.BitwiseAnd a b -> op2 "bwAnd" a b
          P.BitwiseXor a b -> op2 "bwXor" a b
          P.BitwiseOr a b -> op2 "bwOr" a b
          P.And a b -> op2 "scAnd" a b
          P.Or a b -> op2 "scOr" a b
          P.Assign a aop b -> do
            a' <- go a
            b' <- go b
            return $ a' := aop2op aop a' b'
          --Coerce need no longer be part of the syntax
          P.TypeAnnot pe pt -> do
            let t = desugarT pt
            e <- go pe
            return $ e ::: t
          --e -> error $ "Compiler error: missing case in desugarE: " ++ show e
        po1 primop a = Var primop :$ a
        po2 primop a b =
          Var primop :$ (Var "Pair" :$ a :$
                          (Var "Pair" :$ b :$ Var "Unit"))
        op1 :: Name -> P.E -> De E
        op1 primop a = po1 primop <$> go a
        op2 primop a b = po2 primop <$> go a <*> go b
        aop2op = \case
          P.EqEq -> flip const
          P.PlusEq -> po2 "plus"
          P.MinusEq -> po2 "minus"
          P.MulEq -> po2 "multiply"
          P.DivEq -> po2 "divide"
          P.ModEq -> po2 "modulo"
          P.ShlEq -> po2 "shL"
          P.ShrEq -> po2 "shR"
          P.AndEq -> po2 "bwAnd"
          P.XorEq -> po2 "bwXor"
          P.OrEq -> po2 "bwOr"
    {-
    go = \case
      P.String str -> do
        let len = length str
        handleStaticDataExpr (Array (UInt 8) $ fromIntegral len) $
          structE $ map (EInteger . fromIntegral . ord) str
      --TODO distinguish name types in the AST type?
      --The only valid use of standalone uppercase names is enum values
      P.Con (UIdent nm) -> return $ Var nm
      P.Wild -> throwE WildcardInExprContext
      P.BlockE pss -> BlockE <$> mapM desugarS pss
      P.PlusPlusPost pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        temp <- newDeName "temp"
        return $ BlockE [
          SE $ PVar temp := expr,
          SE $ pat := PrimOp "+" [Var temp,EInteger 1],
          LocalReturn 0 $ Var temp
          ]
      P.MinusMinusPost pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        temp <- newDeName "temp"
        return $ BlockE [
          SE $ PVar temp := expr,
          SE $ pat := PrimOp "-" [Var temp,EInteger 1],
          LocalReturn 0 $ Var temp
          ]
      P.Index arr ix -> po "index" [arr,ix]
      --Fold field accesses into a single Dots
      --That's better done in a later traversal...
      --Note that ideally x = a.b; y = x.c would be caught via symbolic eval
      P.Dot pe (Ident nm) -> do
        e <- go pe
        return $ Dots e [Left nm]
      P.Arrow pe field -> go $ P.Deref pe `P.Dot` field
      --Can now no longer be confused with primfun applications, modulo
      --prefix ident primfuns
      P.App (P.Var (Ident nm)) pe
        | S.member nm prefixPrimfuns -> do
            es <- desugarExplicitTuple pe
            return $ PrimOp nm es
      --However, Con arg also uses P.App:
      P.App (P.Con (UIdent con)) parg -> do
        arg <- go parg
        return $ Con con arg
      P.App f x -> (:$) <$> go f <*> go x
      -- ++x =>
      --block {
      -- x += 1;
      -- localReturn 0 x
      -- }
      --Todo deduplicate
      P.PlusPlusPre pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        return $ BlockE [
          SE $ pat := PrimOp "+" [expr,EInteger 1],
          LocalReturn 0 expr
          ]
      P.MinusMinusPre pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        return $ BlockE [
          SE $ pat := PrimOp "-" [expr,EInteger 1],
          LocalReturn 0 expr
          ]
      --Unary - now has its own primfun
      P.Negate pe -> po "negate" [pe]
      P.Not pe -> po "!" [pe]
      P.BitwiseNot pe -> po "~" [pe]
      --Add a pattern synonym for Deref in E?
      P.Deref pe -> po "deref" [pe]
      --It's not strictly a primop...
      P.AddressOf pe -> po "&_" [pe]
      --We split the alloc ptr into pat and expr here to avoid needing to do
      --so in later stages.
      P.At a b -> do
        a' <- desugarE a
        bp <- desugarP b
        be <- desugarE b
        return $ a' :@ (bp,be)
      P.Mul a b -> po "*" [a,b]
      P.Div a b -> po "/" [a,b]
      P.Mod a b -> po "%" [a,b]
      P.Plus a b -> po "+" [a,b]
      P.Minus a b -> po "-" [a,b]
      P.Shl a b -> po "<<" [a,b]
      P.Shr a b -> po ">>" [a,b]
      --Note only <, <=, ==, != primops are supported
      P.MyLT a b -> po "<" [a,b]
      P.LTE a b -> po "<=" [a,b]
      P.MyGT a b -> po "<" [b,a]
      P.GTE a b -> po "<=" [b,a]
      P.Eq a b -> po "==" [a,b]
      P.NEq a b -> po "!=" [a,b]
      P.BitwiseAnd a b -> po "&" [a,b]
      P.BitwiseXor a b -> po "^" [a,b]
      P.BitwiseOr  a b -> po "|" [a,b]
      --Desugar to block expressions
      --a && b =>
      --block {
      -- if a
      -- then localReturn 0 truthy b
      -- else localReturn 0 0
      -- }
      --Note a and b may contain explicit local returns, so their return
      --index needs to be incremented.
      P.And a b -> do
        a' <- incLRDepth 0 <$> go a
        b' <- incLRDepth 0 <$> go b
        return $ BlockE [
          Ifte a' (LocalReturn 0 $ PrimOp "truthy" [b'])
            (LocalReturn 0 $ EInteger 0)
          ]
      P.Or a b -> do
        a' <- incLRDepth 0 <$> go a
        b' <- incLRDepth 0 <$> go b
        return $ BlockE [
          Ifte a' (LocalReturn 0 $ EInteger 1)
            (LocalReturn 0 $ PrimOp "truthy" [b'])
          ]
      --Desugar += etc to block expressions
      --TODO opt: *p.a.b.c += e to avoid duplicating the address calc
      --a.b.c |= or ^= could also be easily optimized
      -- +=, *= are less straightforward due to overflow
      P.Assign lhs aop rhs -> do
        p <- desugarP lhs
        e <- desugarE rhs
        case aop of
          P.EqEq ->
            return $ p := e
          _ -> do
            let primop = case aop of
                           P.PlusEq -> "+"
                           P.MinusEq -> "-"
                           P.MulEq -> "*"
                           P.DivEq -> "/"
                           P.ModEq -> "%"
                           P.ShlEq -> "<<"
                           P.ShrEq -> ">>"
                           P.AndEq -> "&"
                           P.XorEq -> "^"
                           P.OrEq -> "|"
            --Note string allocation is duplicated here; opt to get rid of it
            oldp <- desugarE lhs
            return $ p := PrimOp primop [oldp,e]
      P.Coerce e t -> Coerce (desugarT t) <$> go e
      P.TypeIs e t -> TypeIs (desugarT t) <$> go e
      P.UnsafeCoerce e t -> UnsafeCoerce (desugarT t) <$> go e
    po nm es = PrimOp nm <$> mapM go es
-}

--"abc" => (&sv :: Ptr Code (Array 3 Byte)) where sv := array (97,98,99)
handleString :: String -> De E
handleString str = do
  let codes = map ord str
      len = fromIntegral $ length str
  --Better than silently truncating...
  complainIf (any (>255) codes)
    $ NonByteChar str
  --sv := array cs
  let arrayE = EArray $ map (EInteger . fromIntegral) codes
  s <- get
  --Alloc new name for sv, insert new sv def
  let n = anonStaticCtr s
      svnm = "$static" ++ show n
  put s{anonStaticCtr = n + 1,
        static = M.insert svnm arrayE $ static s}
  return $ (Var "ampersand" :$ Var svnm)
    ::: Ptr Code (Array (TyNat len) (TyCon "Byte"))

--String literals are lifted to staticData decls:
--"abc" becomes staticData (Byte[3]) {97,98,99};
--staticData t e expressions are desugared further to
--newname : Ptr Code t with an accompanying
--staticData t newname = e
--declaration.
{-
Permitted static exprs:
k (integer constants),
-k (negation can be applied statically),
var: function, constructor, staticdata name
&global, &staticdata
tuple --desugars to con apps
Con arg

In theory arbitrary expressions could be permitted, but something like
&global + k would require a more expressive linker - better to keep the
limitations explicit and leave it to the programmer to implement their own
custom creation script logic when necessary.
-}
