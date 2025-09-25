{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Structured.Convert where

import AST.DTs hiding (Var,Unit,Pair)
{-(Pat(),E(),S(),T(..),Name(),Module(..), pattern UInt,
                pattern (:->), pattern Array)-}
import AST.Util (unrollTyApps)
import qualified AST.DTs as A
import Structured.DTs --(Stmt(),Structured())
import qualified Structured.DTs as S
import Mono.Mono (MonoS(..),instT)
import Const.Serialize
import Core.RestrictedCore

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad (forM)

--Converts each C function to the structured IR, breaking up subexprs into a
--flat sequence of assignments and making stack explicit.
--The const values for each global initializer and datatype tag have also been
--computed, enabling case => ifte opts.
--Algo:
--for each (f,(t,(p,s))) in exploredFuns, convert its s to structured Stmts
convert :: (Module,MonoS,Map (Name,[T]) Integer, SerS) -> Structured
convert monoS = error "todo"

--Read: Module, MonoS, sizeof info, SerS
type ConvertR = (Module,MonoS,Map (Name,[T]) Integer, SerS)
--State: scope + stmts (it's just convenient to have in State)
--Also need to alloc new vars
data ConvertS = CS {
  csAllocCtr :: Int,
  csScope :: [Var], --the stack vars, hd = top of stack
  csLoopScopes :: [[Var]], --for declaring scope before a break/continue
  csOutput :: [Stmt]
  }
  deriving (Eq,Ord,Read,Show)
data ConvertError = GenericCE String --placeholder
  deriving (Eq,Ord,Read,Show)
--I don't annot poly names (fs and Cons) with actual type, nor do I do so for
--(:$), so I must reconstruct them from params... a complexity and perf drag.
type Convert = ReaderT ConvertR (StateT ConvertS (Except ConvertError))

--TODO make a class for this, I have a ton of them...
--TODO document anon var naming conventions to prevent clashes
cNewVar :: T -> Convert Var
cNewVar t = do
  s <- get
  let n = csAllocCtr s
  put s{csAllocCtr = n+1}
  return $ Mono ("$v" ++ show n) t

--Only A.Declare modifies the scope.
--I must get the type of each expression, but I don't cache it; if I did so
--at every node or annotated names in E with type this would be simpler.
convertS :: S -> Convert ()
convertS = go
  where go = \case
          --Evaluates e, then pops the result
          A.SE e -> do
            v <- convertE e
            error "todo"

--Each expr returns a single var; it may be split with a copy
--Constant expressions could become a Const bound to a new var.
--Important: that includes functions and global pointers.
--For now, turn leaf consts into const primops; CE later. Indeed, doing so
--by symbolic eval is more general than identifying syntactic consts.
--Static calls can later be detected by symbolic eval.
--Since locals have been unshadowed, they can be translated straightforwardly
--to function params. Emit no code and simply return the var.
--Note the Var contains type info, so no need to return a separate T.
--Invariant: every expr of type t pushes a generated var of type t; any
--subexprs are consumed. I use cleanup for that.
convertE :: E -> Convert Var
convertE = go
  where go = cleanup go'
        go' = \case
          --w: Emit op newvar = Const Word n
          EInteger n ->
            emitOp (Const (UInt 32) $ MkConst (EInteger n)) Unit (UInt 32)
          --A local: dup and return corresponding var
          --Why dup? Because I expect a given stack effect...
          TypedVar (Just t) nm ->
            emitOp (Op "id#" [t]) (Var (Mono nm t)) t
          --Function application: recursively eval f and x, then
          --emit a call (not a primop!)
          f :$ x -> do
            vf <- go f
            vx <- go x
            tf <- cTypeOf f
            let _a :-> b = tf 
            call vf $ Var vx
          --case permits one-level fallible patterns, e.g. Cons True xs
          --The subpatterns True and xs are matched the same way as assignment:
          --If the con doesn't match (as in True = False), revertValue ().
          --Note p may contain subexprs in *e or p!e which must be evaluated
          --before e and bound to anonymous vars.
          --I'll hackily use E Vars to represent them; TODO param Pat by the
          --subexpr type or use a different DT.
          p A.:= e -> do
            p' <- evalPatternEs p
            ve <- go e
            assign p' ve
            return ve
          EArray (Just t) es ->
            mapM go es >>= primMkArray t
          TyApp nm params -> error "todo"
          --Ex: p += k
          --That becomes p' <- eval subexprs in p
          --p' = (interpret as E(p') + k)
          OPAssign (Just opf) p _ e -> do
            --First eval exprs to prevent duplicated side effects
            p' <- evalPatternEs p
            old <- abusedPat2Value p'
            operand <- go e
            --cTypeOf just looks at the f to determine the type of f :$ x,
            --so this works:
            t <- cTypeOf (opf :$ EInteger 0)
            vf <- go opf --A const, so when it's evaluated is irrelevant
            --Note all ops in op assignment are of type (a,a) -> a
            new <- call vf $ Pair (Var old) $ Pair (Var operand) Unit
            assign p' new
            return new
          -- ++x; means {var y = x; x = inc x; y}
          --TODO ensure ++_ et al mention inc in mono!
          --TODO annotate PPPre et al with type, dedup with OPAssign
          PPPre p -> plusplus "inc" True p
          PPPost p -> plusplus "inc" False p
          MMPre p -> plusplus "dec" True p
          MMPost p -> plusplus "dec" False p
          --Eval the given fields in textual order; set the missing ones to
          --null#. Note I then need to support a null# Core primitive!
          --That requires I know the types of each field, which is fortunately
          --easy.
          ConRecord con (Just params) field_es -> do
            --Eval the given fields in textual order
            field2v <- M.fromList <$>
                       forM field_es (\(field,e) -> (,) field <$> go e)
            mod <- cGetModule
            let dtsi = dtsInfo mod
                Just ci = M.lookup con $ conInfo dtsi
                field_ts = conFields ci
                tycon = conParent ci
            --For each field in the constructor, use the given value
            --or null#@[t]() if it's missing.
            vs <- forM field_ts (\(field,t) ->
                                   case M.lookup field field2v of
                                     Nothing -> emitOp (Op "null#" [t]) Unit t
                                     Just v -> return v)
            --Con vs :: TyCon  params
            emitOp (MkCon con params) (vars2value vs) $
              unrollTyApps (TyCon tycon) params
          Dot e (Just params) field -> do
            v <- go e
            t <- typeOfDotE field params
            emitOp (GetField $ NamedField field params) (Var v) t
          e -> error $ "Compiler error: unexpected case in convertE: " ++
               show e
        cleanup :: (E -> Convert Var) -> E -> Convert Var
        cleanup hdlr e = do
          scope <- gets csScope
          v <- hdlr e
          modify (\s->s{csScope = v:scope})
          return v

--Each emitted stmt must be preceded by a scope declaration.
--That is the state of the stack before the stmt, rather than the scope it
--needs.
--Note stmts are stored in reverse order and must be reversed when collected
--into a block.
emitStmt :: Stmt -> Convert ()
emitStmt stmt = do
  s <- get
  let output = csOutput s
      scope = csScope s
  put s{csOutput = stmt : S.Declare scope : output}

--Emits a Core op, binding its result to a single new var. Doesn't specify
--the stack/scope effect.
--It takes its result type as a parameter to give to the Var.
--Note: side-effecting ops may return a tuple containing a mix of dynamic
--and state types. Pair must then be able to store a mix of them, so state
--types are of kind Type!
--Consequence: not all Types are coerce#ible to Bytestring#.
emitOp :: PrimOp -> Value -> T -> Convert Var
emitOp op val t = do
  v <- cNewVar t
  emitStmt (Var v S.:= S.OpE (op,val))
  return v

--Returns the type of an E; if the type is determined by a parameterized name
--(e.g. f, g, Con) it must unfortunately be computed rather than retrieved
--from a cache in the AST itself.
--Precondition: the E has already been HM'd and monomorphized.
cTypeOf :: E -> Convert T
cTypeOf = \case
  EInteger _ -> return $ UInt 32
  TypedVar (Just t) _ -> return t
  f :$ _ -> do
    tf <- cTypeOf f
    let a :-> b = tf
    return a
  EArray (Just t) es -> return $ Array (fromIntegral $ length es) t
  TyApp nm ts -> do
    mod <- cGetModule
    let Just (vs,t) = M.lookup nm $ tysigs mod
        Right monoT = instT (M.fromList $ zip vs ts) t
    return monoT
  CaseE {} -> error "No syntactic support yet..."
  OPAssign _ p _ _ -> gop p
  PPPre p -> gop p
  PPPost p -> gop p
  MMPre p -> gop p
  MMPost p -> gop p
  ConRecord con (Just params) _fields -> typeOfConE con params
  Dot _ (Just params) field -> typeOfDotE field params
  where gop = cTypeOfP
--The type of a monomorphized pattern
cTypeOfP :: Pat -> Convert T
cTypeOfP = \case
  PWild (Just t) -> return t
  TypedPVar (Just t) _ -> return t
  Deref (Just [_r,a]) _ -> return a
  PArray (Just t) ps -> return $ Array (fromIntegral $ length ps) t
  --Look up field info, then parent constructor; get polytype of field,
  --then instantiate using params in dt info.
  PDot (Just params) _ field -> typeOfDotE field params
  PBang (Just [_len,a]) _ _ -> return a
  --Look up con info to get rhs, then instantiate using params in dt info
  PCon con (Just params) _ -> typeOfConE con params

--Given a field and its type params, returns the type of a well-typed
--e.field@params.
--Invariant: all boxed fields have been desugared away.
--Do I still store field signatures? Don't use them for now...
--TODO use cached signatures.
--Note: dtRegion in DTInfo makes dtBoxed superfluous.
typeOfDotE :: Name -> [T] -> Convert T
typeOfDotE field params = do
  mod <- cGetModule
  let dtsi = dtsInfo mod
      Just fi = M.lookup field $ fieldInfo dtsi
  case fi of
    IsTag False tycon ->
      let Just dti = M.lookup tycon $ datatypes dtsi
          ts = dtTagScheme dti
      in case ts of
           Nil -> error $ "Compiler error: tag of untagged DT " ++ tycon
           N1 len -> return $ UInt $ fromIntegral len
           N16 -> return $ UInt 1
           Custom t _ ->
             --Now we need to instantiate the t
             let vs = dtParams dti
                 v2t = M.fromList $ zip vs params
                 Right monoT = instT v2t t
             in return monoT
    IsNormal False tycon con ->
      let Just ci = M.lookup con $ conInfo dtsi
          Just fieldT = lookup field $ conFields ci
          Just dti = M.lookup tycon $ datatypes dtsi
          vs = dtParams dti
          v2t = M.fromList $ zip vs params
          Right monoT = instT v2t fieldT
      in return monoT
    fi | fiBoxed fi -> error $ "Compiler error: unexpected boxed field in "
                       ++ "typeOfDotE: " ++ field ++ " " ++ show params

--Given a Con and its params, returns the type of a well-typed Con{...} record.
--Precondition: the Con is unboxed (the boxed ones should've been desugared
--away).
typeOfConE :: Name -> [T] -> Convert T
typeOfConE con params = do
  mod <- cGetModule
  let dtsi = dtsInfo mod
      Just ci = M.lookup con $ conInfo dtsi
      conT = conRHS ci
      tycon = conParent ci
      Just dti = M.lookup tycon $ datatypes dtsi
      vs = dtParams dti
      v2t = M.fromList $ zip vs params
      Right monoT = instT v2t conT
  if conBoxed ci
    then error $ "Compiler error: unexpected boxed con in typeOfConE: " ++
         con ++ " " ++ show params
    else return monoT

--Gets the Module, which contains much of the info necessary for compilation
cGetModule :: Convert Module
cGetModule = do
  (mod,_mono,_sizeof,_ser) <- ask
  return mod

--evalPatternEs converts a syntactic pattern which may contain subexprs such
--as (arr!ix(), (*p()).field) to
--x <- ix(), y <- p()
--(arr!x,(*y).field).
--That's necessary to prevent e.g. (arr!ix())++ from evaluating ix() twice.
evalPatternEs :: Pat -> Convert EvaluatedPat
evalPatternEs = error "todo"

--A pattern after exprs have been evaluated.
--Its form is restricted to preclude Con{..} (.field | !ix)* which is
--nonsensical.
--BCon {bfield: p} => Unbox (UBCon {ubfield: p})
data EvaluatedPat = EPWild T
                  --Locals become vars in Structured; they're still viewed as
                  --mutable in the abstraction because it's pre-SSA
                  | EPLocal Var [Field]
                  | EPDeref Var --the fields have been baked into the ptr
                  | EPCon Name [T] [(Name,EvaluatedPat)]
                  | Unbox EvaluatedPat
  deriving (Eq,Ord,Read,Show)
--An abused pat has two uses: assigning a value to it and interpreting it as
--an E. Instead of creating an abused E, it's simpler to interpret it
--directly.
--Problem: what about boxed constructors? Evaluating an abused pat should
--consistently produce the same value and have no side effects.
--Consider (Nil :: List ()) |= 0x10_00_00
--Solution: disallow boxed constructors in abusedPat2Value.
abusedPat2Value :: AbusedPat -> Convert Var
abusedPat2Value = error "todo"

--assign implements matching of a pattern p to a value (var) v.
--It's central to pattern matching in case and assignment operations.
--In contrast to Haskell, EVMC case supports only one-level case distinction;
--subpatterns are matched using assign and will revert rather than go to the
--next candidate pattern if they fail. That's to avoid the problem of
--selecting an efficient matching order in composite patterns (for now).
{-Behavior:
Con{field: p} = v =>
 if Con is boxed:
  ImplTyCon ptr = v
  ImplCon{implTyCon_field: p} = *ptr
 else: case tag scheme Con of
  Nil: return ()
  other: require v's tag == Con's tag
 for (field,p) in pattern: p = v.field
TODO opt: if mem remains the same, (*p).field ~ *(GetPtrField p field)
TODO boxed con pattern => deref mentioned

.field | !ix have different behavior for locals and derefs; I should convert
*p (.field | !ix)* to a single *v in the abused pattern.
However, local!foo()!bar() needs to save both foo and bar.
Ideally I'd just save a slice offset (essentially a byte pointer into a
stack var).
-}
assign :: AbusedPat -> Var -> Convert ()
assign (AP p) v = go p v
  where go p v =
          case p of
            PWild{} -> return _
            _ -> error "todo"
            
--The array creation op on vars (evaluated exprs).
--FW: eagerly compress at the word level, as otherwise the stack could grow
--large.
--When assigning a large array literal to a pointer, it would also be worth
--eagerly writing.
primMkArray :: T -> [Var] -> Convert Var
primMkArray = error "todo"

--Converts a list of vars to a tuple value
vars2value :: [Var] -> Value
vars2value = foldr Pair Unit . map Var

--Emits a call (ret = f x). However, it also needs to pass and take the env to
--encode side effects! Passing the env is done after Structured, because
--before passing everything I must create the return continuation.
--The Value may be a tuple.
call :: Var -> Value -> Convert Var
call vf vx = do
  let Mono _ (a :-> b) = vf
  retv <- cNewVar b
  --(retv,env) = Call vf vx 
  let retLHS = Pair (Var retv) (Pair envV Unit)
  emitStmt (retLHS S.:= Call vf vx)
  return retv

--Deduplicates the logic for ++_ et al
--Parameters: inc (++) or dec (--), old or new value returned
plusplus :: Name -> Bool -> Pat -> Convert Var
plusplus incdec prefix p = do
  p' <- evalPatternEs p
  old <- abusedPat2Value p'
  let Mono _nm t = old
      opf = TyApp incdec [t]
  vf <- convertE opf
  new <- call vf (Var old)
  assign p' new
  return $ if prefix
           then old
           else new
