{-# LANGUAGE LambdaCase #-}
module Desugar.SEP where

import qualified E.Abs as P
import AST.DTs
import AST.Util (unrollApps,roll)
import Desugar.DTs
import Util
import Desugar.Util (defaultFieldName)
import Desugar.T

import qualified Data.Set as S
import qualified Data.Map as M hiding ((!))
import Control.Monad.Except

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
desugarE :: DInfo -> P.E -> Either DError E
desugarE di@DInfo{diGlobalSet = gs,
                  diStringNumbering = str2id,
                  diDTsInfo = dtsi
                 } = go
  where
    dot e = Dot e Nothing
    go = \case
      P.EmptyTuple -> return $ Var "Unit"
      P.Tuple pe pes -> tupleE <$> (mapM go $ pe:pes)
      --Integers are sugar for fromWord #w, where w is :: Word
      P.HexInt (P.HexInteger str) -> go $ P.Int $ read str
      P.Int n -> return $ Var "fromWord" :$ EInteger n
      P.Var (Ident nm)
        --g => *g
        | S.member nm gs -> return $ Var "deref" :$ Var nm
        | let -> return $ Var nm
      P.String str ->
        --str => *g
        case M.lookup str str2id of
          Just id -> return $ Var "deref" :$ (Var $ "$string"++show id)
          Nothing -> error $ "Compiler error: unmapped string " ++ str
      --A standalone Con.
      --If there is no such Con, error.
      --If it's underapplied, error.
      --If it's boxed, desugar to ImplTyCon (...).
      P.Con (UIdent con) -> desugarConApp di con []
      P.ConRecord (UIdent con) efields -> do
        es <- mapM (\(P.EField (Ident nm) pe) -> ((,) nm) <$> go pe)
              efields
        return $ ConRecord con Nothing es
      --I'll choose to disallow _ in an expr context for now
      P.Wild -> throwError WildcardInExprContext
      --By deferring decomposition of p++ et al to lets (necessary
      --because the p may contain exprs which should be evaluated once,
      --not twice) we can avoid having lets in E.
      --That simplifies initial desugaring, but complicates the type
      --checker slightly.
      P.PlusPlusPost pp -> PPPost <$> desugarP di pp
      P.MinusMinusPost pp -> MMPost <$> desugarP di pp
      --indexPtr must take the ptr as its first argument to preserve eval
      --order.
      P.Index pptr pix -> do
        ptr <- go pptr
        ix <- go pix
        return $ Var "deref" :$ Var "indexPtr" :$ ptr :$ ix
      --Critical decision: field access is not represented as a function
      --application.
      P.Dot struct (Ident f) -> do
        --Look up the field info
        --TODO deduplicate with P.Dot case in desugarP
        let fsi = fieldInfo dtsi
        fi <- case M.lookup f fsi of
          Nothing -> throwError $ UndefinedFieldInExprDot f
          Just fi -> return fi
        if fiBoxed fi
          then do
          let tycon = fiParentTyCon fi
          --Old scheme: bdt.f => *(bdt.fieldImplCon1).fStructCon
          --New scheme: look up tycon,
          -- *(bdt.unImpl<tycon>).impl<tycon>_f
          bdt <- go struct
          let unboxedField =
                case fi of
                  IsTag {} -> "tagImpl" ++ tycon
                  _ -> "impl" ++ tycon ++ "_" ++ f
          return $ (Var "deref" :$
                    ((bdt `dot` ("unImpl" ++ tycon)))) `dot`
            unboxedField
          else do
            dt <- go struct
            return $ dt `dot` f
      P.Bang arr ix -> op2 "indexArray" arr ix
      --e->field => (*e).field as in C
      P.Arrow e (Ident f) -> go $ P.Deref e `P.Dot` Ident f
      --I use Array (a,b,c) as hacky syntax for array exprs
      --Why (a,b,c) and not Array a b c? Because the former makes
      --recursive desugaring easy and cheap: no need to backtrack based
      --on whether the expr being applied is Array/Struct.
      {-
      P.App (P.Con (UIdent "Array")) ptup ->
        case ptup of
          P.EmptyTuple -> return $ EArray Nothing []
          P.Tuple pe pes -> do
            es <- mapM go $ pe : pes
            return $ EArray Nothing es
          _ -> throwError $ GenericDError "malformed array expr"
      P.App (P.Con (UIdent "Struct")) ptup -> do
              let structE [] = Var "Unit"
                  structE (e:es) = Var "Append" :$ e :$ structE es
              case ptup of
                P.EmptyTuple -> return $ structE []
                P.Tuple pe pes -> do
                  es <- mapM go $ pe : pes
                  return $ structE es
                _ -> throwError $ GenericDError "malformed struct expr"
-}
      --First roll the P.Apps into f ...args to get a bird's eye view.
      --If f is a Con, go to desugarConApps
      --Otherwise desugar f and args and unroll.
      P.App pf px -> do
        let (pf',args) = rollPApps (P.App pf px)
        case pf' of
          P.Con (UIdent con) -> desugarConApp di con args
          _ -> unrollApps <$> go pf' <*> mapM go args
      P.PlusPlusPre p -> PPPre <$> desugarP di p
      P.MinusMinusPre p -> MMPre <$> desugarP di p
      P.Negate a -> op1 "negate" a
      P.Not a -> op1 "lNot" a
      P.BitwiseNot a -> op1 "bwNot" a
      P.Deref a -> op1 "deref" a
      P.AddressOf a -> op1 "addressOf" a
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
      P.Assign pp aop pe -> do
        p <- desugarP di pp
        e <- go pe
        if aop == P.EqEq
          then return $ p := e
          --Hacky but terse replacement for a big case:
          else let op = read $ drop 2 $ show aop
               in return $ OPAssign Nothing p op e
      --Coerce need no longer be part of the syntax
      P.TypeAnnot pe pt -> do
        let t = desugarT pt
        e <- go pe
        return $ e ::: t
    op1 fnm pe = (Var fnm :$) <$> go pe
    op2 fnm pa pb = do
      a <- go pa
      b <- go pb
      return $ Var fnm :$ tupleE [a,b]

--Gets the function being repeatedly applied and collects its arguments:
--Given f a b ... z :: P.E , returns (f,[a,b,...z]).
--Used to enforce that constructors must be fully applied.
rollPApps :: P.E -> (P.E,[P.E])
rollPApps = roll (\case P.App f x -> Just (f,x)
                        _ -> Nothing)

--A helper for constructor applications Con ...args,
--used for standalone Con and applications.
--If con is Array or Struct, args must be [a syntactic tuple].
--If the con is not defined, error.
--If it's underapplied, error.
--If it's overapplied but not MkFun, error.
--If it's boxed, desugar to
--ImplTyCon {unImplTyCon: ImplCon {implTyCon_field: e}}.
desugarConApp :: DInfo -> Name -> [P.E] -> Either DError E
desugarConApp di@(DInfo{diDTsInfo=dtsi}) con args
  | con `elem` ["Array","Struct"] = do
    let err = ArrayAndStructTakeASyntacticTuple con args
    case args of
      [ptup] -> do
        mes <- desugarTup di desugarE ptup 
        case mes of
          Just es ->
            return $ case con of
              "Array" -> EArray Nothing es
              "Struct" -> structE es
          Nothing -> throwError err
      _ -> throwError err
  | let = case M.lookup con $ conInfo dtsi of
            Nothing -> throwError $ NoSuchCon con
            Just ci -> do
              let arity = length $ conFields ci
                  len = length args
              --If underapplied, fail
              complainIf (arity > len)
                $ UnderappliedCon con arity len
              --Desugar the args and split them into the first arity es and
              --the rest.
              es <- mapM (desugarE di) args
              let (eargs,erest) = (take arity es, drop arity es)
              --If overapplied, require con == MkFun
              complainIf (len > arity && con /= "MkFun")
                $ OverappliedNonMkFun con arity es
              let tycon = conParent ci
                  fields = map fst $ conFields ci
                  record = if conBoxed ci
                              --Boxed: ImplTyCon (allocValue ImplCon
                              -- {implTyCon_field: e})
                           then ConRecord ("Impl"++tycon) Nothing
                                [("unImpl"++tycon,
                                  Var "allocValue" :$
                                   ConRecord ("Impl"++con) Nothing
                                   (zip (map (("impl"++tycon++"_")++) fields)
                                    $ eargs)
                                 )
                                ]
                                --Unboxed: Con {field: e}
                           else ConRecord con Nothing $ zip fields eargs
              return $ unrollApps record erest
            
--Used for Struct (a,b,c...) and Array (a,b,c...) in both
--desugarE and desugarP.
desugarTup :: DInfo -> (DInfo -> P.E -> Either DError a) -> P.E ->
  Either DError (Maybe [a])
desugarTup di handler = \case
  P.EmptyTuple -> return $ Just []
  P.Tuple pe pes -> Just <$> mapM (handler di) (pe:pes)
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
desugarP :: DInfo -> P.E -> Either DError Pat
desugarP di@DInfo{diGlobalSet = gs,
                  diDTsInfo = dtsi,
                  diStringNumbering = str2id
                 } = go
  where
    go = \case
      P.Wild -> return $ PWild Nothing
      P.Var (Ident v) ->
        if S.member v gs
        then return $ Deref Nothing $ Var v
        else return $ PVar v
      P.Deref e -> Deref Nothing <$> desugarE di e
      P.EmptyTuple -> return unit
      P.Tuple e es -> tupleP <$> mapM go (e:es)
      --bdt.field => look up field's parent tycon,
      -- *(bdt.unImpl<tycon>).impl<tycon>_field
      --Ooh, consequence: (f()).field becomes a valid LHS for assignment.
      --That's a bit surprising but fine; C++ allows it.
      P.Dot struct (Ident field) -> do
        let fsi = fieldInfo dtsi
        --TODO dedup with analogous desugaring in desugarE
        fi <- case M.lookup field fsi of
                Nothing -> throwError $ UndefinedFieldInPatternDot field
                Just fi -> return fi
        if fiBoxed fi
          then do
          let tycon = fiParentTyCon fi
          e <- desugarE di struct
          --Appending Impl<tycon> instead of prepending it would make the
          --name of the unboxed datatype fields more consistent...
          let unboxedField =
                case fi of
                  IsTag {} -> "tagImpl" ++ tycon
                  _ -> error $ "impl" ++ tycon ++ "_" ++ field
          return $ Deref Nothing
            (Dot e Nothing $ "unImpl" ++ tycon)
            :. unboxedField
          else do
          p <- go struct
          return $ p :. field
      P.Bang arr ix -> (:!) <$> go arr <*> desugarE di ix
      P.Arrow e (Ident f) -> go $ P.Deref e `P.Dot` Ident f
      P.ConRecord (UIdent con) efields -> do
        es <- mapM (\(P.EField (Ident nm) pe) -> ((,) nm) <$> go pe)
              efields
        return $ PCon con Nothing es
      pe -> goCon pe
    goCon pe = do
      (con,ps) <- unrollConApps pe
      return $ PConArgs con Nothing ps
    unrollConApps = \case
      P.App pf px -> do
        x <- go px
        (con,ps) <- unrollConApps pf
        return $ (con,ps ++ [x]) --TODO fix quadratic
      P.Con (UIdent con) -> return (con,[])
      pe -> throwError $ GenericDError $ "Invalid pattern: " ++ show pe
    --mkTup = mkStruct . map (\p -> PConArgs "WordPad" Nothing [p])
    mkStruct :: [Pat] -> Pat
    mkStruct = foldr (\a tup -> PConArgs "Append" Nothing [a,tup]) unit
    unit = PConArgs "Unit" Nothing []

desugarS :: DInfo -> P.S -> Either DError S
desugarS di = go
  where go = \case
          P.SE pe -> SE <$> goe pe
          P.If i t e -> Ifte <$> goe i <*> go t <*> go e
          P.While e s -> While <$> goe e <*> go s
          P.Return e -> Return <$> goe e
          P.Do ss -> Block <$> mapM go ss
          P.Case e cases -> Case <$> goe e <*>
            mapM desugarCase cases
          P.Break -> return Break
          P.Continue -> return Continue
          P.For pre cond post body ->
            go $ P.Do [pre,P.While cond $ P.Do [body,post]]
          P.Declare vbs -> Declare <$> mapM desugarVB vbs
        goe = desugarE di
        gop = desugarP di
        desugarCase (P.C p s) = (,) <$> gop p <*> go s
        desugarVB = \case
          --var x; => var x = null()
          P.JustVar (Ident v) -> return (v,Var "null" :$ Var "Unit")
          P.VarIs (Ident v) e -> (,) v <$> goe e
