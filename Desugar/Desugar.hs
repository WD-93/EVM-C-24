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
import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)

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
desugarFieldP :: P.Field -> De (Maybe Name,Pat)
desugarFieldP = \case
  P.Named (Ident nm) e -> do
    p <- desugarP e
    return (Just nm, p)
  P.Anon e -> do
    p <- desugarP e
    return (Nothing, p)
-}
--Now struct fields need pad,alignment,mnm,e
--Niggle: even if different pad or alignment info has no effect on runtime
--repr, the types are distinct.
{-
desugarField :: (P.E -> De a) -> P.Field -> De (Field a)
desugarField de = go Nothing Nothing
  where go mpad mal = \case
          P.AnnotPad p f
            | Just p' <- mpad -> throwE $ DuplicatePads p' $ P.AnnotPad p f
            | P.Bit <- p -> throwE BitPaddingDeprecated
            | let -> go (toPad p) mal f
          P.AnnotAlign p f
            | Just p' <- mal -> throwE $ DuplicateAligns p' $ P.AnnotAlign p f
            | P.Bit <- p -> throwE BitPaddingDeprecated
            | let -> go mpad (toPad p) f
          P.Named (Ident nm) e -> do
            x <- de e
            return ((deflt mpad, deflt mal), Just nm, x)
          P.Anon e -> do
            x <- de e
            return ((deflt mpad, deflt mal), Nothing, x)
        deflt = \case
          Nothing -> Byte
          Just p -> p
        toPad = Just . \case
          P.Bit -> Bit
          P.Byte -> Byte
          P.Word -> Word
-}
{-
_, x, {p | field:p,...}, (p1,p2,...)
-}
desugarP :: P.E -> De Pat
desugarP = error "todo"
{-
desugarP = do
  let r = desugarP
  \case
    P.Index ptr ix -> desugarP $ (P.PrefixOp (Infix "*") $
                                  P.Ops ptr (Infix "+") (OSNil ix))
    --Assign makes no sense
    --FW ops: !! ~ _[_]
    --FW prefix op: *_, -_
    --For now, there are no Con ps applications
    P.Var (Ident nm) -> return $ PVar nm
    --For now, no Con patterns
    --Dot makes sense, but unsupported for now
    --FW: integer constants
    P.EmptyTup -> return $ PTup []
    P.Tup e es -> PTup <$> ((:) <$> r e <*> mapM r es)
    P.EmptyStruct -> return $ PStruct []
    P.EStruct fields -> PStruct <$> mapM desugarFieldP fields
    P.Wild -> return PWild
    P.Dot p (Ident field) -> PDot <$> r p <*> return field
    P.Hash p n -> PHash <$> r p <*> return (fromInteger n)
    P.PrefixOp (Infix "*") e -> Deref <$> desugarE e
    e -> throwE $ BadEInPat e
-}

--DTs.S now has a concept of standalone do blocks...
desugarBlock :: P.S -> De [S]
desugarBlock =
  \case P.Do ss -> mapM desugarS ss
        s -> (:[]) <$> desugarS s
desugarS :: P.S -> De S
desugarS = \case
  P.SE (P.Assign lhs aop rhs) -> error "TODO"
    --(:=) <$> desugarP lhs <*> desugarE rhs
  P.SE e -> (PWild :=) <$> desugarE e
  P.If e th el -> Ifte <$> desugarE e <*> desugarBlock th <*> desugarBlock el
  P.While e body -> While <$> desugarE e <*> desugarBlock body
  P.Return e -> Return <$> desugarE e
  P.Do ss -> Block <$> desugarBlock (P.Do ss)
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
      P.Struct efields -> error "todo"

--Allocates $static<n> off anonStaticCtr
newAnonStaticName :: De Name
newAnonStaticName = do
  s <- get
  let n = anonStaticCtr s
  put s{anonStaticCtr = n + 1}
  return $ "$static" ++ show n
  
{-
desugarE = do
  let r = desugarE
  \case
    --For now I always desugar a[b] to *(a + b) because that simplifies
    --ptr[ix].field* = e in IR1
    P.Index ptr ix -> desugarE (P.PrefixOp (Infix "*") $
                               P.Ops ptr (Infix "+") (OSNil ix))
    --Assign is not an expr, but should it be...?
    --Pro: that's what C does; it gives you neat puns
    --Con: it's not a higher-level description of an existing EVM pattern, but
    --rather a C feature imposed on the EVM;
    --side effects not as explicit
    P.Assign l r -> throwE $ AssignIsNotAnE l r
    --Special handling of e :: t, the coercion operator
    --No handling of e :: t1 :: t2 for now
    --(::) mixed with other operators => parse failure
    P.Ops e (Infix "::") (OSNil te) ->
      Coerce <$> desugarT te <*> desugarE e
    P.Ops _ (Infix op) os
      | let os2ops (OSNil _) = []
            os2ops (OSCons _ (Infix op) os) = op:os2ops os,
        "::" `elem` (op:os2ops os) -> throwE $ CoerceMixedWithOps (op:os2ops os)
    --For now, use constant fixity info. FW: gather and process fixity decls
    --before desugaring Es.
    P.Ops e (Infix op) os -> do
      e1 <- r e
      opes <- desugarOpsE op os
      return $ opsToApps opPrecedenceInfo e1 opes
    --1-arity constructor allocation, the only type allowed.
    P.App (P.App (P.Con (UIdent con)) parg) ppat -> do
      arg <- desugarE parg
      p <- desugarP ppat
      return $ Con con arg p
    --Hack: BNFC doesn't like adding a hexadecimal number token, so I'll
    --use hex("deadbeef") instead
    P.App (P.Var (Ident "hex")) (P.Str str) ->
     EInteger <$> (case readMaybe $ "0x"++str of
                      Just n -> return n
                      Nothing -> throwE $ GenericDError $
                        "Couldn't read hex number in hex(...): " ++ show str)
    P.App f x -> (:$) <$> r f <*> r x
    P.Var (Ident x) -> return $ Var x
    P.Con (UIdent x) -> throwE $ StandaloneConstructorName x
    --return $ Var x --a name's a name to the IR
    P.Dot e (Ident f) -> (:.) <$> r e <*> return f
    P.Hash e n -> (:#) <$> r e <*> return (fromInteger n)
    P.Int n -> return $ EInteger n
    P.Str str -> return $ EString str
    P.EmptyTup -> return $ EStruct []
    P.Tup e es -> tupleE <$> ((:) <$> r e <*> mapM r es)
    P.EmptyStruct -> return $ EStruct []
    P.EStruct fields -> EStruct <$> mapM desugarFieldE fields
    --Prefix ops: * & ! ~ -
    P.PrefixOp (Infix nm) e
      | "*" <- nm ->
       (Var "deref" :$) <$> desugarE e
      | let -> (Var nm :$) <$> desugarE e
    x -> error $ "Missing case in desugarE: " ++ show x

desugarOpsE op = \case
  OSNil e -> do
    x <- desugarE e
    return [(op,x)]
  OSCons e (Infix op') os -> do
    x <- desugarE e
    opes <- desugarOpsE op' os
    return $ (op,x) : opes

--True: binds left. Lower number: higher binding strength.
type PrecInfo = (Bool,Int)
opPrecedenceInfo = M.fromList [
  ("+",(False,6)),
  ("-",(False,6)),
  ("*",(False,5)),
  ("/",(False,5))
                              ]
defaultPrecInfo = (True,10)
--o1 `gtPrec` o2 iff o1 has a lower number or an equal number & o2 binds left
gtPrec :: PrecInfo -> PrecInfo -> Bool
gtPrec (l1,b1) (l2,b2) = b1 < b2 || (b1 == b2 && l2)
--Given a sequence e op e op ... e, converts it to a tree of applications.
--e op e1 OP e2 OP e3 ... if OP binds left e1 may be nested arbitrarily deep.
--a op b OP c ... => a op (...
opsToApps :: Map Name PrecInfo -> E -> [(Name,E)] -> E
opsToApps m e opes = shunt [e] [] opes
  --Shunting yard algo
  --An E can always be constructed since there's no mismatch between #es & #ops
  --Quirk: unlike Haskell's op prec parsing, never fails
  where shunt es ops [] = buildOps es ops
        shunt (b:a:es) (op':ops') ((op,e):opes)
          | op' >? op = shunt (appOp op' a b : es) ops' ((op,e):opes)
        shunt es ops ((op,e):opes) = shunt (e:es) (op:ops) opes
        o1 >? o2 = pinfo o1 `gtPrec` pinfo o2
        pinfo op = case M.lookup op m of
                     Just i -> i
                     Nothing -> defaultPrecInfo
        buildOps [e] [] = e
        buildOps (b:a:es) (op:ops) =
          buildOps (appOp op a b : es) ops
        appOp op a b = Var op :$ tupleE [a,b]
-}
