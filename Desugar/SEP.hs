{-# LANGUAGE LambdaCase #-}
module Desugar.SEP where

import qualified E.Abs as P
import AST.DTs
import AST.Util (unrollApps,roll)
import Desugar.DTs
import Util
import Desugar.Util (defaultFieldName)
import Desugar.T
import DeclBucket (Loc(..))
import qualified DeclBucket as DB --for the E' Loc, T' Loc etc synonyms

import qualified Data.Set as S
import qualified Data.Map as M hiding ((!))
import Control.Monad.Except
import Control.Arrow ((***))
--String literals are now unboxed; conversion is done here.
import Data.Char (ord)
import Control.Monad

--Change: I'll split the desugaring into a first pass that takes no context,
--followed by a series of generic everywhereM rewrites on the Module.
--Con args => Con fs can be deferred by converting Con to an invalid Var.
--Underapplication detection must use a stop condition to prevent triggering
--it on f in f :$ x.

--Desugaring functions using DInfo for S, E and Pat respectively.
--Since the datatypes contain each other, they need to be put in one module.
--AST.DTs change: cons don't need to be fully applied?
--They don't need it for type inference, anyway.
--Cons are also no longer relevant to &_.

--desugarE needs to throw errors because CST patterns are expressions which
--may not correspond to AST patterns.
--New invariant: desugarE is never recursively called on a partial application,
--e.g. (f x) in f x y.
--Instead Apps (except Array (e1,e2,...) and Struct (e1,e2,...)) are fully
--rolled into f ...xs before recursive desugaring.
--That's used to enforce full application of every constructor, and
--permit overapplication iff the constructor is MkFun.
--All the constructor arguments are therefore collected before generating the
--constructor application, so they can always be of form Con {field: e}.
--Boxed constructors Con {field: e} are desugared to
--ImplTyCon (allocValue (ImplCon {implTyCon_field: e})).
--HM may then assume Var nm is either a global or function; TODO remove
--the logic for constructors.
desugarE :: DInfo ->
  DB.E -> Either DError E
desugarE di{-@DInfo{diGlobalSet = gs,
                  diStringNumbering = str2id,
                  diDTsInfo = dtsi
                 }-} = go
  where
    dot e = Dot e Nothing
    go = \case
      P.EmptyTuple loc -> go $ cstTupleE loc []
      P.Tuple loc pe pes -> go $ cstTupleE loc $ pe:pes
      --Integers are sugar for fromWord #w, where w is :: Word
      P.HexInt loc (P.HexInteger str) -> go $ P.Int loc $ read str
      P.Int _loc n -> return $ Var "fromWord" :$ EInteger n
      --g => *g is deferred
      P.Var _loc (Ident nm) -> return $ Var nm
        --g => *g
        -- | S.member nm gs -> return $ Var "deref" :$ Var nm
        -- | let -> return $ Var nm
      --Change: string literals are now unboxed.
      --Pro: <=32B strings will be cheaper to use.
      --Con: If you want to refer to them by code pointer, you need to manually
      --declare a code global. For large strings, explicit reference by pointer
      --becomes necessary. allocValue("large string...") should optimize to
      --a codecopy...
      --The advantage for the compiler is that initial desugaring doesn't need
      --any context.
      --The encoding is compatible with UTF-8 for ASCII chars; todo make it
      --fully compatible with Solidity strings.
      P.String _loc str -> do
        let ns = map ord str
        complainIf (any (>255) ns)
          $ NonByteChar str
        return $ EArray Nothing
          [Var "fromWord" :$ EInteger (fromIntegral n)
          | n <- ns]
          --Restricting string literals to be Byte arrays;
          --depends on UInt and Array being defined.
          ::: Array (TyNat $ fromIntegral $ length str) (UInt 1)
        {-
        --str => *g
        case M.lookup str str2id of
          Just id -> return $ Var "deref" :$ (Var $ "$string"++show id)
          Nothing -> error $ "Compiler error: unmapped string " ++ str
        -}
      --A constructor with no arguments
      P.Con loc (UIdent con) -> desugarConAppE di loc con [] {-
        | con `elem` words "Struct Array Pair" ->
            --TODO add proper error
            throwError $ GenericDError $ "Standalone " ++ con
        | otherwise -> 
            desugarConAppE di con [] -}
      --Look up con info.
      --If the con does not exist, error.
      --If any of the fields are not fields of the con, error.
      --If there are duplicate fields, error.
      --If Con {field: e} is boxed, desugar to
      --ImplTyCon (allocValue (ImplCon {implTyCon_field: e}))
      --New approach: defer that, just preserve structure in E for later
      --context-dependent everywhereM rewrites.
      --TODO desugar Pair {fs:es}
      P.ConRecord loc (UIdent con) efields
        | con `elem` ["Struct","Array"] ->
          throwError $ GenericDError $ con ++ " may not be used as a record"
        | otherwise ->
        if con == "Pair"
          then do
          --Pair field to Append field map
          let pf2af = M.fromList[("fst","first"),("snd","second")]
          afs <- forM efields $ \(P.EField loc (Ident nm) pe) ->
            case M.lookup nm pf2af of
              Nothing -> throwError $ GenericDError $
                         "Bad Pair field: " ++ nm
              Just afield -> return $ P.EField loc (Ident afield) $
                             P.ConRecord loc (UIdent "WordPad")
                             [P.EField loc (Ident "unWordPad") pe]
          go $ P.ConRecord loc (UIdent "Append") afs
          else do
          field_es <- mapM (\(P.EField _loc (Ident nm) pe) ->
                              ((,) nm) <$> go pe) efields
          conE di con field_es
      --I'll choose to disallow _ in an expr context for now
      P.Wild _loc -> throwError WildcardInExprContext
      --By deferring decomposition of p++ et al to lets (necessary
      --because the p may contain exprs which should be evaluated once,
      --not twice) we can avoid having lets in E.
      --That simplifies initial desugaring, but complicates the type
      --checker slightly.
      P.PlusPlusPost _loc pp -> PPPost Nothing <$> desugarP di pp
      P.MinusMinusPost _loc pp -> MMPost Nothing <$> desugarP di pp
      --indexPtr must take the ptr as its first argument to preserve eval
      --order.
      P.Index _loc pptr pix -> do
        ptr <- go pptr
        ix <- go pix
        return $ Var "deref" :$ (Var "indexPtr" :$ tupleE [ptr,ix])
      --Critical decision: field access is not represented as a function
      --application.
      --bdt.boxedField desugars to not use boxed fields... so I can share the
      --desugaring and field validity check between exprs and patterns.
      --Params: component desugar (go), deref function, dot function
      --New approach: bdt.field => *(...).implTyCon_field is deferred, so
      --we just preserve the structure here.
      --What about .fst => .first.unWordPad?
      P.Dot _loc struct (Ident f) -> do
        s <- go struct
        --Handling boxed fields and tags...
        case M.lookup f $ diFields di of
          Just fi | fiBoxed fi -> do
                      let tycon = fiParentTyCon fi
                      return $ Dot (Var "deref" :$
                                    (Dot s Nothing "unWordPad")) Nothing $
                        case fi of
                          IsTag {} -> "tagImpl" ++ tycon
                          IsNormal {} -> "impl"++tycon++"_"++f
          _ ->
            return $ Dot s Nothing f
        --do desugarDot (Var "deref" :$) dot go di struct f
      P.Bang _loc arr ix -> op2 "indexArray" arr ix
      --e->field => (*e).field as in C
      P.Arrow loc e (Ident f) -> go $ P.Dot loc (P.Deref loc e) $ Ident f
      --First roll the P.Apps into f ...args to get a bird's eye view.
      --If f is a Con, go to desugarConApps
      --Otherwise desugar f and args and unroll.
      P.App _loc pf px -> --(:$) <$> go pf <*> go px
        do
          let (pf',args) = rollPApps (P.App _loc pf px)
          case pf' of
            P.Con loc (UIdent con) -> desugarConAppE di loc con args
            _ -> unrollApps <$> go pf' <*> mapM go args
      P.PlusPlusPre _loc p -> PPPre Nothing <$> desugarP di p
      P.MinusMinusPre _loc p -> MMPre Nothing <$> desugarP di p
      P.Negate _loc a -> op1 "negate" a
      P.Not _loc a -> op1 "lNot" a
      P.BitwiseNot _loc a -> op1 "bwNot" a
      P.Deref _loc a -> op1 "deref" a
      P.AddressOf _loc a -> op1 "addressOf" a
      P.Mul _loc a b -> op2 "multiply" a b
      P.Div _loc a b -> op2 "divide" a b
      P.Mod _loc a b -> op2 "modulo" a b
      P.Plus _loc a b -> op2 "plus" a b
      P.Minus _loc a b -> op2 "minus" a b
      P.Shl _loc a b -> op2 "shL" a b
      P.Shr _loc a b -> op2 "shR" a b
      P.MyLT _loc a b -> op2 "lt_" a b
      P.LTE _loc a b -> op2 "lte_" a b
      P.MyGT _loc a b -> op2 "gt_" a b
      P.GTE _loc a b -> op2 "gte_" a b
      P.Eq _loc a b -> op2 "eq_" a b
      P.NEq _loc a b -> op2 "neq_" a b
      P.BitwiseAnd _loc a b -> op2 "bwAnd" a b
      P.BitwiseXor _loc a b -> op2 "bwXor" a b
      P.BitwiseOr _loc a b -> op2 "bwOr" a b
      P.And _loc a b -> op2 "scAnd" a b
      P.Or _loc a b -> op2 "scOr" a b
      P.Assign _loc pp aop pe -> do
        p <- desugarP di pp
        e <- go pe
        case aop2op aop of
          Nothing -> return $ p := e
          Just op -> return $ OPAssign Nothing p op e
      --Coerce need no longer be part of the syntax
      P.TypeAnnot _loc pe pt -> do
        let t = desugarT pt
        e <- go pe
        return $ e ::: t
    op1 fnm pe = (Var fnm :$) <$> go pe
    op2 fnm pa pb = do
      a <- go pa
      b <- go pb
      return $ Var fnm :$ tupleE [a,b]

--If Append, WordPad or Unit are not defined, desugaring tuples should throw
--NoSuchCon; failing to do so will lead to a compiler error in
--Desugar.Desugar.boxedConDesugaring.
--Instead of converting CST tuples to AST con applications directly, we must
--convert to CST con applications and recurse.
--tupleE considered harmful? No, it's still useful in later phases.
--Need to pass origin loc as well...
cstTupleE :: Loc -> [DB.E] -> DB.E
cstTupleE loc = foldr (cstPair loc) $ P.Con loc $ UIdent "Unit"
cstPair :: Loc -> DB.E -> DB.E -> DB.E
cstPair loc a b = (con "Append" $$ (con "WordPad" $$ a)) $$
                  (con "WordPad" $$ b)
  where con nm = P.Con loc (UIdent nm)
        ($$) = P.App loc
cstStruct :: Loc -> [DB.E] -> DB.E
cstStruct loc = foldr append $ con "Unit"
  where append a b = (con "Append" $$ a) $$ b
        con nm = P.Con loc (UIdent nm)
        ($$) = P.App loc
unrollCSTApps :: Loc -> DB.E -> [DB.E] -> DB.E
unrollCSTApps loc f = foldl ($$) f
  where ($$) = P.App loc

--EqEq does not correspond to an Op
--Maybe I should rename PlusEq-MinusEq to AddEq-SubEq to keep the name length
--consistent for all ops except Or.
aop2op :: P.AOp' loc -> Maybe Op
aop2op = \case
  P.EqEq _loc -> Nothing
  aop -> Just $ case aop of
                  P.PlusEq _loc  -> Plus
                  P.MinusEq _loc -> Minus
                  P.MulEq _loc   -> Mul
                  P.DivEq _loc   -> Div
                  P.ModEq _loc   -> Mod
                  P.ShlEq _loc   -> Shl
                  P.ShrEq _loc   -> Shr
                  P.AndEq _loc   -> And
                  P.XorEq _loc   -> Xor
                  P.OrEq _loc    -> Or

desugarDot :: (E -> e) -> (e -> Name -> e) ->
              (DB.E -> Either DError e) ->
              DInfo -> DB.E -> Ident -> Either DError e
desugarDot deref dot go di struct (Ident f) = error "todo" {-do
  --Look up the field info
  let dtsi = diDTsInfo di
      fsi = fieldInfo dtsi
  fi <- case M.lookup f fsi of
          Nothing -> throwError $ UndefinedFieldInDot f
          Just fi -> return fi
  if fiBoxed fi
    then do
    let tycon = fiParentTyCon fi
    --Old scheme: bdt.f => *(bdt.fieldImplCon1).fStructCon
    --New scheme: look up tycon,
    -- *(bdt.unImpl<tycon>).impl<tycon>_f
    bdt <- desugarE di struct
    let unboxedField =
          case fi of
            IsTag {} -> "tagImpl" ++ tycon
            _ -> "impl" ++ tycon ++ "_" ++ f
    let edot = flip Dot Nothing
    return $ deref ((bdt `edot` ("unImpl" ++ tycon))) `dot` unboxedField
    else do
    dt <- go struct
    return $ dt `dot` f -}

--Useful in both desugarE and desugarP; a is ignored.
--If the con does not exist, error.
--If the record has a field that does not belong to the con, error.
--If there are duplicate fields, error.
checkRecordValidity :: DInfo -> Name -> [(Name,a)] -> Either DError ()
checkRecordValidity di con field_as =
  case M.lookup con $ diConFields di of
    Nothing -> throwError $ NoSuchCon con
    Just fields -> do
      let expectedFields = S.fromList fields
          fieldList = map fst field_as
          actualFields = S.fromList fieldList
          conflict = S.difference actualFields expectedFields
      complainIf (not $ S.null conflict)
        $ FieldsDoNotMatchConInRecord con conflict
      let fieldCounts = count fieldList
          badCounts = M.filter (>1) fieldCounts
      complainIf (not $ M.null badCounts)
        $ DuplicateFieldsInRecord con badCounts

--Gets the function being repeatedly applied and collects its arguments:
--Given f a b ... z :: P.E , returns (f,[a,b,...z]).
--Used to enforce that constructors must be fully applied.
rollPApps :: P.E' loc -> (P.E' loc, [P.E' loc])
rollPApps = roll (\case P.App _loc f x -> Just (f,x)
                        _ -> Nothing)

--A helper for constructor applications Con ...args,
--used for standalone Con and applications.
--If con is Array or Struct, args must be [a syntactic tuple].
--If the con is not defined, error.
--If it's underapplied, error.
--If it's overapplied but not MkFun, error.
--If it's boxed, desugar to
--ImplTyCon {unImplTyCon: ImplCon {implTyCon_field: e}}.
--To fully dedup with its pattern equivalent, I would need to apply the
--desugaring to patterns. That would require an &&(ImplCons {...}) underef
--pattern. I'll write a separate desugarConAppP for now and then compare...
--The Array and Struct cases are almost identical, but Con args does not
--permit overapplication in patterns.
desugarConAppE :: DInfo -> Loc -> Name -> [DB.E] -> Either DError E
desugarConAppE =
  desugarConApp desugarE (EArray Nothing)
  {-
  (\a b rest -> return $
    unrollApps (ConRecord "Append" Nothing
                 [("first", ConRecord "WordPad" Nothing
                            [("unWordPad",a)]),
                   ("second", ConRecord "WordPad" Nothing
                              [("unWordPad",b)])]) rest)-} --Pair a b handler
  (\con fields len arity eargs erest -> do
      --If overapplied, require con == MkFun
      complainIf (len > arity && con /= "MkFun")
        $ OverappliedNonMkFun con arity (eargs ++ erest) --es reconstructed
      --conE redundantly checks con validity, but it's convenient...
      --Besides, defensive programming is good.
      --record <- conE dtsi con $ zip (map fst $ conFields ci) eargs
      let record = ConRecord con Nothing $ zip fields eargs
      return $ unrollApps record erest)
--Con args => Con {field: e} regardless of whether it's boxed.
--Overapplied constructors are never accepted.
desugarConAppP :: DInfo ->
  Loc -> Name -> [DB.E] -> Either DError Pat
desugarConAppP =
  desugarConApp desugarP (PArray Nothing)
  {-
  (\a b rest ->
     case rest of
       [] -> return $
         PCon "Append" Nothing [("first", PCon "WordPad" Nothing
                                          [("unWordPad",a)]),
                                 ("second", PCon "WordPad" Nothing
                                            [("unWordPad",b)])
                               ]
       _ -> throwError $ OverappliedPatternCon "Pair" 2 $ a:b:rest)
-}
  (\con fields len arity pargs prest -> do
      complainIf (len > arity)
        $ OverappliedPatternCon con arity $ pargs ++ prest
      return $ PCon con Nothing $ zip fields pargs
  )

desugarConApp :: (DInfo -> DB.E -> Either DError e) ->
  ([e] -> e) ->
  --([e] -> e) -> --struct
  --(DB.E -> DB.E -> [DB.E] -> Either DError e) -> --pair
  (Name -> [Name] -> Int -> Int -> [e] -> [e] -> Either DError e) ->
  --end of P/E args
  DInfo -> Loc -> Name -> [DB.E] -> Either DError e
desugarConApp go array build
  di@(DInfo{diConFields=cfs}) loc con args =
  ifArrOrStruct go array di loc con args $
  case M.lookup con cfs of
            Nothing -> throwError $ NoSuchCon con
            Just fields -> do
              let arity = length fields
                  len = length args
              --If underapplied, fail
              complainIf (arity > len)
                $ UnderappliedCon con arity len
              --Desugar the args and split them into the first arity es and
              --the rest.
              es <- mapM (go di) args
              let (eargs,erest) = (take arity es, drop arity es)
              --Everything above this can be shared.
              --Params: dtsi, con, eargs, erest
              build con fields len arity eargs erest
--This should also handle Pair.
--Pair, Pair a => underapplied con Pair
--Pair a b => Append {first: WordPad a, second: WordPad b}
--Overapplied: the pair handler errors for Pat
ifArrOrStruct :: (DInfo -> DB.E -> Either DError e) ->
                 ([e] -> e) ->
                 --([e] -> e) -> --struct
                 -- (DB.E -> DB.E -> [DB.E] -> Either DError e) -> --pair
                 DInfo -> Loc -> Name -> [DB.E] ->
                 Either DError e ->
                 Either DError e
ifArrOrStruct go array di loc con args alt
  | con == "Pair" = do
      --Only the first two args of Pair get word-padded before application
      --Because we're generating a new CST, we need a loc param...
      --Inefficiency: we roll CST apps, then unroll, only to roll again in go.
      case args of
        a:b:rest -> go di $ unrollCSTApps loc (cstPair loc a b) rest
        _ -> throwError $ UnderappliedCon "Pair" 2 $ length args
  | con `elem` ["Array","Struct"] = do
    let err = ArrayAndStructTakeASyntacticTuple con args
    --Because Struct (...) should complain when Append is undefined,
    --struct must operate on CSTs so we can recurse on it with go.
    case args of
      [ptup] -> do
        let mpes = cstTup ptup
        case mpes of
          Just pes ->
            case con of
              "Array" -> do
                array <$> mapM (go di) pes
              "Struct" -> go di $ cstStruct loc pes
          Nothing -> throwError err
      _ -> throwError err
  | otherwise = alt

--A helper for generating the desugaring of boxed Con {field: e}
--given datatype info. It takes dtsi rather than ci to make it possible to
--call without an in-place M.lookup.
--If the Con is a boxed constructor of datatype TyCon, it desugars to
--ImplTyCon (allocValue (ImplCon {implTyCon_field: e})).

--New: just checks the given fields match the constructor and contain no
--duplicates; does not desugar BCon to ImplBCon (...)
conE :: --DTsInfo e ->
  DInfo ->
  Name -> [(Name,E)] -> Either DError E
conE di con field_es = do
  checkRecordValidity di con field_es
  return $ ConRecord con Nothing field_es
  {-
conE dtsi con field_es = do
  checkRecordValidity dtsi con field_es
  case M.lookup con $ conInfo dtsi of
    --Nothing case eliminated
    Just ci ->
      let tycon = conParent ci
      in return $ if conBoxed ci
      --Boxed: ImplTyCon (allocValue ImplCon {implTyCon_field: e})
      then ConRecord ("Impl"++tycon) Nothing
           [("unImpl"++tycon,
             Var "allocValue" :$
             ConRecord ("Impl"++con) Nothing
             (map ((("impl"++tycon++"_")++) *** id) field_es)
            )
           ]
           --Unboxed: Con {field: e}
      else ConRecord con Nothing field_es-}

--Used for Struct (a,b,c...) and Array (a,b,c...) in both
--desugarE and desugarP.
cstTup :: DB.E -> Maybe [DB.E]
cstTup = \case
  P.EmptyTuple _ -> Just []
  P.Tuple _ pe pes -> Just $ pe:pes
  _ -> Nothing
desugarTup :: DInfo -> (DInfo -> DB.E -> Either DError a) ->
              DB.E ->
              Either DError (Maybe [a])
desugarTup di handler pe =
  case cstTup pe of
    Just es -> Just <$> mapM (handler di) es
    _ -> return Nothing

{-
Valid patterns:
_, x, *e, p.field, p!e, Con a b c, Con {field: p}

Desugaring:
Array tup => EArray
Struct tup => Append a $ Append b ... Unit
() => Unit
(a,...) => Append (WordPad a) $ ... Unit

DInfo-dependent:
bdt.f => *(...).fStructCon
g => *g
-}
desugarP :: DInfo ->
  DB.E -> Either DError Pat
desugarP di@DInfo{
  diFields = fs
  --diGlobalSet = gs,
  --diDTsInfo = dtsi,
  --diStringNumbering = str2id
                 } = go
  where
    go = \case
      P.Wild _loc -> return $ PWild Nothing
      --g => *g substitution will be performed in a later pass
      P.Var _loc (Ident v) -> return $ PVar v
        {-
        if S.member v gs
        then return $ Deref Nothing $ Var v
        else return $ PVar v
-}
      P.Deref _loc e -> Deref Nothing <$> desugarE di e
      P.EmptyTuple _loc -> return $ tupleP []
      P.Tuple _loc e es -> tupleP <$> mapM go (e:es)
      --bdt.field => look up field's parent tycon,
      -- *(bdt.unImpl<tycon>).impl<tycon>_field
      --Ooh, consequence: (f()).field becomes a valid LHS for assignment.
      --That's a bit surprising but fine; C++ allows it.
      --Oh no... that means I must know whether a field is boxed or not in
      --order to avoid attempting to desugar f() as a pattern.
      --I have two options:
      --1) Convert to *($placeholderMark(e)).field,
      --then convert the e to a pattern at a later stage.
      --2) Pass in field boxity info.
      --Fortunately I have that info available in pmFields.
      P.Dot loc struct (Ident f) ->
        case M.lookup f fs of
          Just fi
            | fiBoxed fi -> do
                s <- desugarE di struct
                let tycon = fiParentTyCon fi
                return $ Deref Nothing (Dot s Nothing ("unImpl"++tycon)) :.
                  (case fi of
                      IsTag {} -> "tagImpl" ++ tycon
                      IsNormal {} -> "impl"++tycon++"_"++f)
          _ -> do
            s <- go struct
            return $ s :. f
        --desugarDot (Deref Nothing) (:.) go di struct f
      P.Bang _loc arr ix -> (:!) <$> go arr <*> desugarE di ix
      P.Arrow loc e (Ident f) -> go $ P.Dot loc (P.Deref loc e) $ Ident f
      P.ConRecord _loc (UIdent con) efields -> do
        es <- mapM (\(P.EField _loc (Ident nm) pe) -> ((,) nm) <$> go pe)
              efields
        checkRecordValidity di con es
        return $ PCon con Nothing es
      pe -> do
        let (f,args) = rollPApps pe
        case f of
          P.Con loc (UIdent con) -> do
            desugarConAppP di loc con args
          _ -> throwError $ BadConInPattern f

desugarS :: DInfo ->
  DB.S -> Either DError S
desugarS di = go
  where go = \case
          P.SE _loc pe -> SE <$> goe pe
          P.If _loc i t e -> Ifte <$> goe i <*> go t <*> go e
          P.While _loc e s -> While <$> goe e <*> go s
          P.Return _loc e -> Return <$> goe e
          P.Do _loc ss -> Block <$> mapM go ss
          P.Case _loc e cases -> Case <$> goe e <*>
            mapM desugarCase cases
          P.Break _loc -> return Break
          P.Continue _loc -> return Continue
          P.For loc pre cond post body ->
            --Placeholder locs for now
            go $ P.Do loc [pre,P.While loc cond $ P.Do loc [body,post]]
          P.Declare _loc vbs -> Declare <$> mapM desugarVB vbs
        goe = desugarE di
        gop = desugarP di
        desugarCase (P.C _loc p s) = (,) <$> gop p <*> go s
        desugarVB = \case
          --var x; => var x = null()
          P.JustVar _loc (Ident v) -> return (v,Nothing,Var "null" :$ tupleE [])
          P.VarIs _loc (Ident v) e -> (\e->(v,Nothing,e)) <$> goe e
