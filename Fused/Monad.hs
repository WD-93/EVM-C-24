{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase,
TypeFamilies #-} --for Construct
module Fused.Monad where

--The monads used for implementing the fused phase
--(monomorphization, structured compilation, sizeof computation, serialization,
--global layout).

import AST.DTs
import qualified AST.DTs as A
import Const.Const
import Structured.DTs
import qualified Structured.DTs as IR
import Core.RestrictedCore
import Core.PrimTypes
import Mono.Mono (instT,bindT,BindError(..))
--The Construct monad, allowing overloaded straight-line code defs:
import Construct (Construct(op,constant,Op))
import qualified Construct as CM
--EVM opcode info lets one automate the Construct instance's behavior for
--all valid straight-line ops.
import OpcodeInfo (State(..),
                   OpcodeInfo(..),
                   OpcodeBehavior(..),
                   Effect(..),
                   opcodes)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Data.Char (toLower) --OpcodeInfo.State -> state var naming convention

--The main monad:
--Monomorphization, structured IR generation, datatype sizeof calculation,
--const serialization and global layout interleaved in one phase.
--Simple solution: a RWSE monad
--No need for a capability class, just lift when in FusedFunM?
newtype FusedM a = FM {runFusedM :: ReaderT Module
                     (StateT FusedS (Except FusedError)) a
                   }
  deriving (Functor, Applicative, Monad,
            MonadReader Module,
            MonadState FusedS,
            MonadError FusedError
           )
type MonoT = (Name,[T])
data FusedS = FS {
  --To prevent infinite loops in recursive funs
  fsVisitedFuns :: Set (Name,[T]),
  --Will be copied to Structured
  fsDefuns :: Map FunVar (BranchValue,[Stmt]),
  --To prevent infinite loops in code g = <e that depends on g>
  fsVisitedGlobals :: Set Name,
  --Code global g => label g(offset: 0, len: 2) : Ptr Code t
  --other g => off : Ptr r t
  --The code global's initializer is also included.
  --Q: Should I trim right-padding when placing datatypes in bytecode?
  fsGlobals :: Map Name (Region, T, Maybe Serialized),
  --Datatypes:
  fsVisitedDatatypes :: Set MonoT,
  --We currently don't record internal padding
  fsSizeof :: Map MonoT Integer,
  --Monomorphized E recorded for symbolic opts
  --fsTags :: Map (Name,[T]) (E,Serialized), --Con@ts => tag
  fsTagSchemes :: Map (Name,[T]) ([Name], TagScheme (E,Serialized)),
  --field@ts => ...
  fsOffsets :: Map (Name,[T]) (Integer, --off for UBCons
                               Integer, --size of field
                               T --monomorphic type
                              ),
  --A general-purpose counter; used for allocating IR var names to start with.
  fsCtr :: Integer,
  --All functions, globals and datatypes reachable from main:()->() must be
  --explored. Each category may mention any of the others.
  --A cyclical unboxed datatype such as data Foo = {Foo Foo} should trigger
  --an exception, so we need to use a stack of tycons to detect loops when
  --exploring datatypes.
  --However, data Foo = {Foo}; tag Foo = ()->() where {Foo: f}; f() := Foo
  --should *not* raise an exception.
  --Similarly, tag Foo = Ptr Code Foo where {Foo: &g}; code g = Foo should
  --work.
  --A naive recursive exploration therefore won't do; we must spawn function
  --and code global exploration tasks instead of running them directly.
  --fsRunQueue is the queue of such tasks.
  fsRunQueue :: [AsyncTask]
  }
  deriving (Eq,Ord,Read,Show)
--All globals must be spawned; though non-code globals don't have an
--initializer to explore, the sizeof their referenced type must be determined
--to be finite.
--TODO: cache defs in task constructor
data AsyncTask = ExploreGlobal Name
               | ExploreFunction (Name,[T])
               | SerializeAllocValue (Name,T,E)
  deriving (Eq,Ord,Read,Show)
spawnExploreG :: Name -> FusedM ()
spawnExploreG = spawn . ExploreGlobal
spawnExploreF :: (Name,[T]) -> FusedM ()
spawnExploreF = spawn . ExploreFunction
--Serializes a constExpr, binding it to the given name in fsGlobals
spawnSerializeAllocValue :: (Name,T,E) -> FusedM ()
spawnSerializeAllocValue = spawn . SerializeAllocValue
--Note we don't need a fair scheduler, exploration should be order-independent.
spawn :: AsyncTask -> FusedM ()
spawn task = do
  s <- get
  put s{fsRunQueue = task : fsRunQueue s}

initFusedS = FS {
  fsVisitedFuns = S.empty,
  fsDefuns = M.empty,
  fsVisitedGlobals = S.empty,
  fsGlobals = M.empty,
  fsVisitedDatatypes = S.empty,
  fsSizeof = M.empty,
  --fsTags = M.empty,
  fsTagSchemes = M.empty,
  fsOffsets = M.empty,
  fsCtr = 0,
  fsRunQueue = []
  }
data FusedError = GenericFE String
                | NoMain
                | IlltypedMain BindError T
                | CyclicalDatatypes [MonoT]
                | ArbitraryDatatypeStackDepthExceeded MonoT
                --Ran getFieldInfo before exploreD:
                | CompilerErrorFieldInfoBeforeExploreD Name [T]
                | AssignmentToImmutableRegion T
                | NotAssignableLHS String
                --I can't use EvaluatedPat here atm... need to move it lower in
                --dependency hierarchy.
                | MultiwordStackArrayAssign Integer T
                | MultiwordStackArrayIndex Integer T
                | NotSerializableExpr E
                | NonCodeAllocInSerialize T E
                | GlobalPointerSpaceExhaustedBy Name Integer
                --Opcode-specific:
                | UnrecognizedOpcode String [Var]
                | NotAStraightLineOp String [Var] OpcodeBehavior
                | BadOpArity String [Var] Int
                | OpMustReturnAWord String [Var]
                | Op0MayNotReturnAWord String [Var]
                --addressOf-specific (&e):
                | AddressOfCan'tHandle E
  deriving (Eq,Ord,Read,Show)

--Compiling f: S -> E <-> P
--In addition to the capabilities of FusedM, the FusedFunM monad must
--have additional state: the scope and inLoop. It must also emit Stmts.
data FusedFunR = FFR (Name,[T])
data FusedFunS = FFS {ffsScope :: [Var],
                      ffsInLoop :: Bool
                     }
  deriving (Eq,Ord,Read,Show)
newtype FusedFunM a = FFM {runFFM :: ReaderT FusedFunR
                            (WriterT [Stmt]
                             (StateT FusedFunS
                              FusedM)) a
                          }
  deriving (Functor, Applicative, Monad,
            MonadReader FusedFunR,
            MonadWriter [Stmt],
            MonadState FusedFunS,
            MonadError FusedError)
liftFused :: FusedM a -> FusedFunM a
liftFused m = FFM $ lift $ lift $ lift m
unliftFFM :: FFM a -> FusedFunR -> FusedFunS ->
             FusedM (a,FusedFunS,[Stmt])
unliftFFM ffm ffr ffs = do
  ((a,stmts),ffs') <- flip runStateT ffs $
                      runWriterT $
                      flip runReaderT ffr $
                      runFFM ffm
  return (a,ffs',stmts)
--Alloc off the general-purpose counter
alloc :: FusedM Integer
alloc = do
  fs <- get
  let n = fsCtr fs
  put fs{fsCtr = n + 1}
  return n

--TODO use capability classes
--The MonadError instance for FusedFunM should have its error wrapped in
--InFun (reader input f) when run in FusedM.

getScope :: FusedFunM [Var]
getScope = gets ffsScope
putScope :: [Var] -> FusedFunM ()
putScope scope = modify (\ffs->ffs{ffsScope=scope})

--Given a dest list and a source list of Word Vars, copies source to dest.
--If the lengths are unequal, that's a compiler error.
--No type checking is done; it can be used to coerce
copyTo :: [Var] -> [Var] -> FusedFunM ()
copyTo dst src
  | length dst /= length src = error "Compiler error in copyTo"
  | otherwise = zipWithM_ (\to from ->
                             emitPrim ([to],[]) "copy" ([from],[])) dst src
--I got tired of typing FusedFunM
type FFM = FusedFunM
--Copies the given word var to a new var with the given type; TODO rename to
--coerceVar.
copy :: T -> Var -> FFM Var
copy t v = do
  w <- newVar t
  copyTo [w] [v]
  return w
--Copies the given vars to new vars of type W t 1..n; is valid to use when
--the number of source vars matches the word size of t.
--To be used in word-shuffling ops which change type such as construct or
--destruct.
coerceVars :: T -> [Var] -> FFM [Var]
coerceVars t vs =
  let wts = [W t $ TyNat $ fromIntegral n | n <- [1..]]
  in zipWithM copy wts vs
  
--Copy vars without modifying the type
copyVars :: [Var] -> FFM [Var]
copyVars xs = do
  ys <- mapM (\(Mono x t) -> newVar t) xs
  copyTo ys xs
  return ys

--Emits a primop with the given lhs and rhs
emitPrim :: Value -> Name -> Value -> FusedFunM ()
emitPrim lhs primop rhs = tell [lhs IR.:= (Op primop, rhs)]

--Emits an EVM op that consumes two words and pushes a Word, with no additional
--effects to track. Autogens the lhs.
op2 :: Name -> Var -> Var -> FusedFunM Var
op2 primop a b = do
  v <- newVar (W (UInt 32) 1)
  emitPrim ([v],[]) primop ([a,b],[])
  return v
--Ditto for 1 argument
op1 :: Name -> Var -> FusedFunM Var
op1 primop a = do
  v <- newVar (W (UInt 32) 1)
  emitPrim ([v],[]) primop ([a],[])
  return v

--TODO take FFM's as argument to allow ergonomic expr construction?
--shl by k bytes; negative k => shr instead.
--Always zero for k > 31 or < -31
--Note shr, shl take the shift value first!
(<<<) :: Integral n => Var -> n -> FFM Var
v <<< k
  | k <= -32 = pushK 0
  | k < 0 = do
      vk <- pushK (fromIntegral k * (-8))
      op2 "shr" vk v
  | k == 0 = return v
  | k < 32 = do
      vk <- pushK (fromIntegral k*8)
      op2 "shl" vk v
  | k >= 32 = pushK 0
maskBytes :: Integer -> Var -> FFM Var
maskBytes k v
  | k < 0 = pushK 0
  | k >= 32 = return v
  | let = do
          vk <- pushK (256^k-1)
          op2 "and" vk v

--Ors the given vars together
disjunction :: [Var] -> FFM Var
disjunction = foldlOp "or" (pushK 0) 
conjunction :: [Var] -> FFM Var
conjunction = foldlOp "and" (pushK 1)
--Combines the given words with a primop; returns a default expr if the list
--is empty.
--Can be used for conjunction, disjunction, sum...
foldlOp :: Name -> FFM Var -> [Var] -> FFM Var
foldlOp op dflt = \case
  [] -> dflt
  v:vs -> go v vs
    where go v = \case
            [] -> return v
            v':vs -> do
              w <- go v' vs
              op2 op v w


--Adds k to the given word
addK :: Integer -> Var -> FFM Var
--This opt will become redundant once I add symbolic eval opt
addK 0 v = return v
addK k v = do
  kv <- pushK k
  op2 "add" kv v
--In addition to their stack arguments,
--the mem write ops consume $mem : MemSlice# and update it.
--In the optimizer, I'll need to mark the ops as consuming rather than simply
--taking their SElem argument.
mstore :: Var -> Var -> FFM ()
mstore off w = CM.op0 "mstore" [off,w]
mstore8 :: Var -> Var -> FFM ()
mstore8 off b = CM.op0 "mstore8" [off,b]
mcopy :: Var -> Var -> Var -> FFM ()
mcopy dst src len = CM.op0 "mcopy" [dst,src,len]

--The C == operator inlined; returns a Bool
--TODO Core opts: move branch earlier if a_i /= b_i is likely, speculatively
--short-circuiting the computation.
--Opt 2: as != bs :: Word = the disjunction of their pairwise xors, avoiding an
--iszero if reverting on inequality (as in tag checks on assignment).
--jumpi cond fail, fail: jump revertValue,... can be optimized to jumpi cond
--revertValue@[()] via inlining.
--Opt 3: negate the jumpi cond if that leads to a nicer code layout, e.g.
--fallthrough to code that other functions jump to (so no fallthrough
--contention).
equals :: [Var] -> [Var] -> FFM Var
equals as bs
  --TODO move the Fused.Monad datatypes to a lower module so Pretty can import
  --them and the combinators can use ppr'd vars without a cycle?
  --Better alt: turn GenericFE calls into separate error constructors,
  --do the string-processing in the CLI UI.
  | length as /= length bs =
    throwError $ GenericFE $
    "Compiler error: as and bs have different lengths in Fused.Monad.equals: "
    ++ show (as,bs)
  | let = zipWithM (op2 "eq") as bs >>=
          conjunction >>=
          copy (W (TyCon "Bool") 1)
          
--Always returns a W (UInt 32) 1, i.e. a Word.
--Truncated to 32B.
--Precondition: n >= 0 (EVMC expresses negative numbers as negation of
--positive ones).
pushK :: Integer -> FusedFunM Var
pushK n = do
  let ser = serWord n
  w <- newVar $ W (UInt 32) 1
  tell [([w],[]) IR.:= (Push ser, ([],[]))]
  return w
--Pushes a global or function label of C type T
pushLabel2 :: Name -> [T] -> T -> FFM Var
pushLabel2 nm ts t = do
  let ser = serLabel2 nm ts
  w <- newVar $ W t 1
  tell [([w],[]) IR.:= (Push ser, ([],[]))]
  return w
--Pushes a Serialized value (assumed to be of sizeof <= 32)
pushSer :: Serialized -> T -> FFM Var
pushSer ser t = do
  w <- newVar t
  tell [([w],[]) IR.:= (Push ser, ([],[]))]
  return w
--Pushes the lower 32B of a Serialized value
pushSerWord :: Serialized -> T -> FFM Var
pushSerWord ser t
  | serSizeof ser == 0 = pushSer emptySer t
  | let = let w = last $ splitSer ser
          in pushSer w t
--Used for pushing a tag, which may be 0 or more words
--First split the serialized into words, then pushSer them
pushMultiWordSer :: Serialized -> T -> FFM [Var]
pushMultiWordSer ser t = do
  let ixsers = zip [1..] $ splitSer ser
  forM ixsers (\(n,ser) -> pushSerWord ser (W t $ TyNat n))

--The scope information is embedded in the stmt by the caller
emitStmt :: Stmt -> FFM ()
emitStmt stmt = tell [stmt]
--For embedding debugging info in the generated code:
comment :: String -> FFM ()
comment = emitStmt . Comment

--Generates a new Var with the given Core type
newVar :: T -> FusedFunM Var
newVar t = do
  n <- liftFused alloc
  return $ Mono ("$anon"++show n) t

--TODO add $mem to lhs/rhs in mem ops;
--do the same for other impure ops
--With OpcodeInfo.opcodes, I can now derive the behavior of each opcode.
--Only instructions with Normal behavior are acceptable ops.
--Their arity can be checked, and their state var lhs+rhs auto-generated.
--An opcode called in 'op' must return a word; one called in 'op0' must not.
--Convention: state vars are taken and returned in S.fromList order.
instance Construct FusedFunM where
  type Var FFM = Var
  type Op FFM = String
  op primop vs = do
    mv <- runOp primop vs
    case mv of
      Nothing -> throwError $ OpMustReturnAWord primop vs
      Just v -> return v
  op0 primop vs = do
    mv <- runOp primop vs
    case mv of
      Just v -> throwError $ Op0MayNotReturnAWord primop vs
      Nothing -> return ()
  --TODO move collect to Fused.Monad...
  ifte nret cond th el = do
    --The name of the value returned; both branches will assign their value
    --to vs, a parallel of SSA phi var assignment.
    --A default value need not be passed.
    xs <- sequence $ replicate nret $ newVar $ UInt 32
    scope <- getScope
    let coll b m =
          snd <$> collect scope (do ys <- m
                                    if length ys /= length xs
                                      then throwError $ GenericFE $
                                           "Length mismatch in ifte " ++
                                           show b ++ ": " ++ show (nret,ys)
                                      else return ()
                                    copyTo xs ys)
    ths <- coll True th
    els <- coll False el
    emitStmt $ IR.Ifte scope [] cond ths els
    putScope $ xs ++ scope
    return xs
  constant = pushK
  comment = comment

--Isolate stmt emission and scope effect; used for compiling iftes.
collect :: Scope -> FFM a -> FFM (a,[Stmt])
collect scope ffm = do
  cache <- getScope
  pass $ do
    putScope scope
    (a,stmts) <- listen ffm --collect the emitted stmts
    putScope cache
    return ((a,stmts), const []) --intercept them

runOp :: String -> [Var] -> FFM (Maybe Var)
runOp primop vs =
  case M.lookup primop opcodes of
    Nothing -> throwError $ UnrecognizedOpcode primop vs
    Just oi -> do
      do let len = length vs
             ar = oiArgArity oi
         if (len /= ar)
           then throwError $ BadOpArity primop vs ar
           else return ()
      case oiBehavior oi of
        Normal {obReturns = b,
                obEffect = Effect consumes produces
               } -> do
          mv <- if b
                then Just <$> newVar (W (UInt 32) 1)
                else return Nothing
          emitPrim ([v | Just v <- [mv]], stateVars produces)
            primop
            --FFM doesn't care whether input state is consumed or borrowed,
            --that's for Stack scheduling of instructions.
            (vs, stateVars $ M.keysSet consumes)
          return mv
        other -> throwError $ NotAStraightLineOp primop vs other
stateVars :: Set OpcodeInfo.State -> [Var]
stateVars ss = map toVar $ S.toList ss
  where toVar s =
          let str = show s
          in Mono ("$"++map toLower str)
             (TyCon $ str ++ "State")
