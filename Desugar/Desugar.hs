{-# LANGUAGE LambdaCase #-}
module Desugar.Desugar where
--A separate module for desugaring; Compiler should just tie each stage
--together and handle the IO.


--import E.Par (pM,myLexer)
--import E.ErrM (Err(..))
import E.Abs (Ident(..),UIdent(..))
import qualified E.Abs as P

--CST -> AST
import AST.DTs
--AST -> AST
import Desugar.Transforms

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)
import Data.Char (ord) --for string desugaring

data DError = TySigDefunMismatch Name Name
            | DuplicateDefun Name
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
            | MalformedPatternField P.EField
  deriving (Eq,Ord,Read,Show)

desugar :: P.M -> Either DError Module
desugar (P.Module ds) =
  case runState (runExceptT $ desugarDs ds) $
  Module {defuns = M.empty,
          tysyns = M.empty,
          static = M.empty,
          globals = [],
          datatypes = M.empty,
          constructors = M.empty,
          enums = M.empty,
          enumValues = M.empty,
          anonStaticCtr = 0
         } of
    (Left derr, _) -> Left derr
    (Right (), m) -> Right m
--Every defun f must be preceded by a tysig f : t; together they become one
--DT.Defun.
--Duplicate defuns are an error.
type De = ExceptT DError (State Module)
desugarDs :: [P.D] -> De ()
desugarDs [] = return ()
desugarDs (P.TySyn conargs te : rest) = do
  let (nm,args) = desugarConArgs conargs
  let t = desugarT te
  modify (\m -> m{tysyns = M.insert nm (args,t) $ tysyns m})
  desugarDs rest
desugarDs (P.TySig (Ident f) t :
           P.Defun (Ident f') lhs s :
           rest)
  | f /= f' = throwE $ TySigDefunMismatch f f'
  | let = do
          checkForDuplicates f
          let t' = desugarT t
          --Note patterns are a subset of syntactically valid Es
          p <- desugarP lhs
          --Need to add do block support to DTs?
          s' <- desugarS s
          insertDefun f (t',p,s')
          desugarDs rest
--Decision: fixed-size arrays are now a first-class type; array globals no
--longer decay to pointers.
--Catch arr[len > 65536] in desugarT
desugarDs (P.Global pr (Ident x) pt : rest) = do
  checkForDuplicates x
  let r = TyCon $ show pr
  let t = desugarT pt
  s <- get
  put s{globals = globals s ++ [(x,r,t)]} --I know it's quadratic...
  desugarDs rest
desugarDs (P.Data lhs rhs : rest) = do
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
  error "todo"
desugarDs other = throwE $ BadDOrdering other

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
desugarConLHS :: P.ConLHS -> (Name,[Name])
desugarConLHS = go
  where go = \case
          P.CLNil (UIdent tycon) (Ident rparam) -> (tycon,[rparam])
          P.CLCons conlhs (Ident param) ->
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
desugarConRHS :: (Name,[Name]) -> [P.DataCon] -> De [(Name,T)]
desugarConRHS (tycon,r:params) cons =
  mapM (\(tag,(P.DC (UIdent con) parg)) -> do
           let arg = desugarT parg
           addConstructor con (tag,arg,tycon,r,params)
           return (con,arg)
       ) $ zip [0..] cons

--Adds the info of a new constructor to the constructors map; throws an error
--if there's a duplicate. Constructors do not conflict with tysyns or tycons.
addConstructor :: Name -> (Int, T, Name, Name, [Name]) -> De ()
addConstructor con info = do
  mod <- get
  let cons = constructors mod
  if M.member con cons
    then throwE $ DuplicateConstructors con
    else put mod{constructors = M.insert con info cons}

--No decls (functions, tysyns, datatypes, globals, immutables...) may shadow
--each other.
--TODO add primfuns.
--Potential opt: split check for lowercase names and constructors
checkForDuplicates :: Name -> De ()
checkForDuplicates nm = do
  m <- get
  --TODO give a more informative error message
  if S.member nm $ S.unions $
    [M.keysSet $ defuns m,
     M.keysSet $ tysyns m,
     M.keysSet $ datatypes m,
     M.keysSet $ enums m,
     M.keysSet $ enumValues m,
     primTyCons]
    then throwE $ DuplicateDeclsForName nm
    else return ()

insertDefun :: Name -> (T,Pat,S) -> De ()
insertDefun f def =
  modify (\m->m{defuns=M.insert f def $ defuns m})

desugarConArgs :: P.ConArgs -> (Name,[Name])
desugarConArgs = \case
  P.CANil (UIdent nm) -> (nm,[])
  P.CACons cargs (Ident arg) ->
    let (nm,args) = desugarConArgs cargs
    in (nm,args++[arg]) --Tiny inefficiency

{-
type SInt = Int Signed
type UInt = Int Unsigned
T ::= Int signedness n
    | T -> T --only op allowed
    | {(T | field:T),...}
FW: Ptr, unparam'd user types
-}
desugarT :: P.T -> T
desugarT = go
  where go = \case
          P.TVar (Ident nm) -> TyVar nm
          P.TNat n -> TyNat n
          P.TCon (UIdent nm) -> TyCon nm
          P.TStruct fields -> Struct $ map desugarFieldT fields
          P.TEmptyTup -> Struct []
          P.TTup t ts -> tupleT $ map go $ t:ts
          P.TApp tf tx -> go tf :$$ go tx
          P.TArray t n -> Array (go t) n
          P.TArrow a b -> go a :-> go b
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

{-
_, x, {p | field:p,...}, (p1,p2,...), *e, e[e], p.field, p#ix
In future: Con p
-}
desugarP :: P.E -> De Pat
desugarP = go
  where go = \case
          P.Struct _ -> todo
          P.EmptyTuple -> return $ PTup []
          P.Tuple p ps -> PTup <$> mapM go (p:ps)
          P.Var (Ident nm) -> return $ PVar nm
          P.Wild -> return PWild
          P.Index arr ix -> PIndex <$> desugarE arr <*> desugarE ix
          P.Dot p (Ident nm) -> PDot <$> go p <*> return nm
          P.Hash p ix -> PHash <$> go p <*> return (fromInteger ix)
          P.Deref e -> Deref <$> desugarE e
          e -> throwE $ MalformedPattern e
        todo = error "todo"
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

desugarS :: P.S -> De S
desugarS = \case
  P.SE e -> SE <$> desugarE e
  P.If e th el -> Ifte <$> desugarE e <*> desugarS th <*> desugarS el
  P.While e body -> While <$> desugarE e <*> desugarS body
  P.Return e -> Return <$> desugarE e
  P.Do ss -> Block <$> mapM desugarS ss
    --throwE $ BadDoInDesugarS ss
  P.Case pe pcases -> do
    e <- desugarE pe
    cases <- mapM desugarCase pcases
    return $ Case e cases

--TODO allow _, x patterns in case
desugarCase :: P.CASE -> De (Name,Pat,S)
desugarCase (P.C pe ps) =
  case pe of
    P.App (P.Con (UIdent con)) ppat -> do
      pat <- desugarP ppat
      s <- desugarS ps
      return (con,pat,s)
    _ -> throwE $ BadPatternInCase pe

--For now I'll leave desugarE in De for simplicity
desugarE :: P.E -> De E
desugarE = go
  where
    go = \case
      P.AnonStaticData pt pe -> do
        let t = desugarT pt
        e <- desugarE pe
        handleStaticDataExpr t e
      P.AnonStaticDatatype pt pe -> do
        let t = desugarT pt
        e <- desugarE pe
        nm <- newAnonStaticName
        handleStaticDatatype t nm e
        return $ Var nm
      P.Struct efields -> EStruct <$> mapM desugarFieldE efields
      P.EmptyTuple -> return $ EStruct []
      P.Tuple pe pes -> tupleE <$> mapM go (pe:pes)
      P.HexInt (P.HexInteger str) -> return $ EInteger $ read str
      P.Int n -> return $ EInteger n
      P.Var (Ident nm) -> return $ Var nm
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
      P.Hash pe ix -> do
        e <- go pe
        return $ Dots e [Right $ fromInteger ix]
      --Can now no longer be confused with primfun applications, modulo
      --prefix ident primfuns
      --However, Con arg also uses P.App:
      P.App (P.Con (UIdent con)) parg -> do
        arg <- go parg
        return $ Con con arg
      P.App f x -> (:$) <$> go f <*> go x
      -- ++x =>
      --block {
      -- x += 1;
      -- localReturn 0 x
      --}
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
      --}
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
    po nm es = PrimOp nm <$> mapM go es
desugarFieldE :: P.EField -> De (Field E)
desugarFieldE = go1
  where go1 = \case
          P.EPad fld -> go2 Word fld
          P.EF1 fld -> go2 Byte fld
        go2 pad = \case
          P.EAlign fld -> go3 pad Word fld
          P.EF2 fld -> go3 pad Byte fld
        go3 pad al = \case
          P.ENamed (Ident nm) pe -> do
            e <- desugarE pe
            return ((pad,al),Just nm,e)
          P.EAnon pe -> do
            e <- desugarE pe
            return ((pad,al),Nothing,e)

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
var: function, enum value, staticdata name
&global
struct
tuple
Con arg

In theory arbitrary expressions could be permitted, but something like
&global + k would require a more expressive linker - better to keep the
limitations explicit and leave it to the programmer to implement their own
custom creation script logic when necessary.
-}

--handleStaticDataExpr allocates the accompanying decl and returns newname
handleStaticDataExpr :: T -> E -> De E
handleStaticDataExpr t e = do
  nm <- newAnonStaticName
  handleStaticData t nm e
  return $ Var nm
--Handles staticData (t) nm = e;
--e : t is placed in code; nm : Ptr Code t points to it
--Note constructor applications, staticData exprs and strings create nested
--static data/type references.
--Strings and staticData/type exprs are handled when desugaring the e, but
--constructor applications are not; they must be handled here.
--The actual layout in terms of bytes and labels is computed after type
--checking; all we need to do here is create the static declaration and
--recursively allocate staticDatatypes.
handleStaticData :: T -> Name -> E -> De ()
handleStaticData t nm e = error "todo"

--Like staticData, but for datatypes (which are boxed).
--staticDatatype (tycon args) nm = Con arg
--places {tag_Con,arg} in code, nm : tycon args Code points to it.
--Note the top-level Con is mandatory, and only tycon args (a datatype without
--the region applied) is an acceptable t parameter.
--As with staticData, 
handleStaticDatatype t nm e = error "todo"

--Recursively allocates staticDatatypes, substituting them for their names as
--in staticDatatype expressions.
--Standalone names are only valid if they're enum values, functions or static
--names, but we don't check that here.
--A feature that would be nice to have in Haskell: union patterns.
--Constraint: equal var set with compatible types.
--That could be used to make a pattern for "valid leaf exprs" here.
--Oh no - to allocate static data for Con arg I need to know the type, but I
--don't know it yet! Better defer that until type checking then.
handleStaticExpr :: E -> De E
handleStaticExpr = go
  where go e =
          case e of
            EInteger _ -> return e
            Var _ -> return e
            --Only valid for globals:
            PrimOp "&_" [Var _] -> return e
            EStruct fields -> EStruct <$> mapMFields go fields
            Con con arg -> error "todo"
--Utility function; todo use it elsewhere
--It just ignores padding and the field name, a common pattern
mapMFields :: (a -> m b) -> [Field a] -> [Field b]
mapMFields f = mapM (\(pad,mnm,a) -> do
                        b <- f a
                        return (pad,mnm,b))

--Allocates $prefix<n> off anonStaticCtr; need a generic version because I
--also need to allocate vars for the desugaring of x++ to
--block {
-- temp = x;
-- x = x + 1;
-- localReturn 0 temp
-- }
--The $ ensures it won't be confused with user variables
newDeName :: String -> De Name
newDeName prefix = do
  s <- get
  let n = anonStaticCtr s
  put s{anonStaticCtr = n + 1}
  return $ "$" ++ prefix ++ show n
newAnonStaticName = newDeName "static"
