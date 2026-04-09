{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, LambdaCase,
 RankNTypes, DeriveFunctor, FlexibleInstances #-}
module Opt.Concurrent where

import Opt.Semilattice

import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except --used to define Concurrent instance
import Control.Monad
import Data.Kind (Type(..))
import Control.Monad.ST
import Control.Monad.Fix
import Data.STRef
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM --used for Consumers

--Experimenting with the AI = increasing vars linked by circuits triggered
--by updates idea.

--Poorer man's concurrency transformer: just need spawn, no yield
--TODO add a prio param?
class Monad m => Concurrent m where
  spawn :: m () -> m ()
  scheduler :: m ()
newtype ConcT m a = ConcT {unConcT :: StateT [ConcT m ()] m a}
  deriving (Functor,Applicative,Monad,MonadFix)
--Handles passing the initial runQueue, but not running the scheduler.
--That's because I want to read the chans in AI after running the scheduler.
runConcT :: Monad m => ConcT m a -> m a
runConcT (ConcT sm) =
  flip evalStateT [] sm
instance Monad m => Concurrent (ConcT m) where
  spawn m = ConcT $ modify (m:)
  scheduler = go
    where go = ConcT get >>= \case
            [] -> return ()
            ms -> ConcT (put []) >> sequence_ (reverse ms) >> go
--Implementing for transformers:
--Problem: to use the underlying spawn, I need to unlift (run) the transformer.
--That doesn't trivially make sense for every transformer.
instance Concurrent m => Concurrent (ExceptT e m) where
  spawn m = lift $ spawn $ runExceptT m >> return ()
  scheduler = lift scheduler
instance HasRef m => HasRef (ConcT m) where
  type Ref (ConcT m) = Ref m
  newRef = lift . newRef
  readRef = lift . readRef
  writeRef r = lift . writeRef r
--Q: Is FIFO more efficient? LIFO would trigger op updates immediately, even
--when other vars would be updated.
instance MonadTrans ConcT where
  lift = ConcT . lift

--Mutable vars that notify consumers on update.
data MutVar m a = MutVar {mvState :: Ref m a,
                          mvConsumers :: Ref m [a -> m ()]
                         }
--Constraint: the Ref type family is parameterized by m, so
--m may have only one ref type instead of refs having one monad.
--Using a class is nicer than having a Ref datatype which contains its own
--methods, since class methods are statically known and can be inlined.
class Monad m => HasRef m where
  type Ref m :: Type -> Type
  newRef :: a -> m (Ref m a)
  readRef :: Ref m a -> m a
  writeRef :: Ref m a -> a -> m ()

readMutVar :: HasRef m => MutVar m a -> m a
readMutVar = readRef . mvState
writeMutVar :: (Concurrent m, HasRef m, Eq a) => MutVar m a -> a -> m ()
writeMutVar mv new = do
  let ref = mvState mv
  old <- readRef ref
  if old /= new
    then do
    fs <- readRef $ mvConsumers mv
    sequence_ [spawn (f new) | f <- fs]
    writeRef ref new
    else return ()
modifyMutVar :: (Concurrent m, HasRef m, Eq a) =>
  (a -> a) -> MutVar m a -> m ()
modifyMutVar f mv = do
  a <- readMutVar mv
  writeMutVar mv $ f a
--Subscribe to updates of a MutVar
subMutVar :: HasRef m => MutVar m a -> (a -> m ()) -> m ()
subMutVar mv f = do
  let ref = mvConsumers mv
  fs <- readRef ref
  writeRef ref (f:fs)

--Circuit patterns:
--With increasing ops and out = fold op ins where op is monotonic and
--idempotent, new in vars can be added incrementally as ins grows.
--Each in is linked to out by in changed => out op= in. I'll call that
--link (|=).
--Ex applicable ops: (||) for reachability, (&&) for inevitability,
--least upper bound of AbVars.
(|=) :: (Concurrent m, HasRef m, Eq a) =>
  MutVar m a -> (a -> a -> a, MutVar m a) -> m ()
outv |= (op,inv) = do
  --Postcondition: outv >= inv
  --First outv op= inv to ensure it holds even before inv is next updated
  a <- readMutVar inv
  modifyMutVar (op a) outv
  subMutVar inv (\a -> modifyMutVar (op a) outv)
--For all elements in a growing set, some equation applies.
--First apply it to each existing element, then to new ones as they're
--added. The callback uses an additional ref to track deltas.
--Ex use:
--Core: bb lhs = let ops in call v,args,ret,scope
--for all f in funs(v):
-- f.args |= args
-- if f may return, ret.scope |= scope
{-
forAll :: (Concurrent m, HasRef m, Ord a) =>
  MutVar m (Set a) -> (a -> m ()) -> m ()
forAll set property = do
  as <- readMutVar set
  forM_ (S.toList as) property
  subDelta set as S.difference (mapM_ property)
subDelta :: HasRef m => MutVar m a -> a -> (a -> a -> b) -> (b -> m ()) -> m ()
subDelta mv init diff callback = do
  tracker <- newRef init
  subMutVar mv (\new -> do
                   old <- readRef tracker
                   writeRef tracker new
                   callback $ diff new old)
-}
--TODO ensure a is ascending by using Ord? It might be nontrivial to verify,
--even if the overall program can be proven to increase the mv.

--Consider y = op xs. If any x in xs changes, y should eventually be
--recalculated. However, that should ideally be done only once if n vars in
--xs change.
--Solution: when any x changes, set a flag and spawn a task if it was false.
--The task fetches all vs <- xs and processes them, then sets the flag back
--to false.
--With FIFO ordering, that should be scheduled efficiently.
--Values (op lhs and rhs) are a tuple rather than a parameterized DT; I'll
--handle them explicitly for now.
type Val a = ([a],[a])
opAssign :: (Concurrent m, HasRef m, Eq a) =>
  Val (MutVar m a) -> --lhs
  (Val a -> Val a) -> --op; no error or bad arity handling for now
  Val (MutVar m a) ->
  m ()
opAssign lhs op rhs = do
  flag <- newRef False
  let callback _ = do
        b <- readRef flag
        if b
          then return ()
          else do
          writeRef flag True
          spawn $ updateHandler >> writeRef flag False
  mapVal (flip subMutVar callback) rhs
  return ()
  where mapVal f (xs,ys) =
          (,) <$> mapM f xs <*> mapM f ys
        updateHandler = do
          (xs,ys) <- mapVal readMutVar rhs
          let (as,bs) = lhs
          zipWithM_ writeMutVar as xs
          zipWithM_ writeMutVar bs ys

--Eliminating intermediate sets in S = union S1 S2: if S1 and S2 both depend
--on the same state it's more efficient to have a single callback.
--Otherwise, they can be represented as streams rather than vars:
--an action S += current S1, then a callback S1 delta => S += delta.
--TODO add DeltaMutVars? Perhaps need a Delta typeclass.
--A stream is implemented as an action applied to a var:
--S += stream becomes run stream with param S.
--As long as the input values and funs applied are monotonic, it doesn't matter
--when the stream is run. Enforcement of that via a typeclass would be nice,
--but intermediate maps needn't be monotonic...
--streamMutVar ~ the initial value and subsequent updates.
--streamDeltas might also be useful.
--Streams support Functor and Applicative; Monad should be avoided since
--the circuit structure and MutVars depended on should be ~fixed.
--Not quite fixed: bb.lhs = union of vars of predecessors bb
--That formulation (one value = f many values) is more elegant than
--"When bb adds successor bb', bb'.lhs += ..." despite requiring an additional
--preds mutvar: the description of bb.lhs is in one place rather than spread
--out over many side effects in source.
--That's true even if you need to implement preds via callbacks on succs.
--reify :: Stream a -> MutVar a would let you ensure the mutvar is defined once
--How to enforce that?
--What is the role of MutVars when Streams can implement the same logic?
--They're like registers in a circuit. Beyond allowing inspection of the
--result, they serve as checkpoints which prevent wasteful recomputation
--and enable termination of fixpoints.
--unreify reify stream can be inserted anywhere in a circuit.
--forAll ~ a fold op :: Stream (Set a) -> Stream a, given a monotonic op
--and a growing set of increasing elements.
--Ex: reachable f = any reachable (preds f)
--fold :: SemiLattice a => Stream (Set a) -> Stream a?

--f.args = fold args (callsites[f])
--Could the callsites map itself be constructed as a single stream?
--Adding new bbs to callsites via a fold might actually be efficient.
--Implem: subscribe to succs of each SLS with a stateful stream; update it
--from false to true when f is added to succs, then unsubscribe.
--That replicates work shared by all preds... it should be possible to use
--a map of subscribers and notify for a set of new fs in n log n.
--Exploit the structure in the fs as well!
--That's reminiscent of the "notify on price >= k" pattern. But how to
--express indexed subscription elegantly?
--It requires an additional circuit node with input deltas and state = a map
--f => stream.
--Does Map support Map k (a -> b) -> Map k a -> Map k b or do I need a new
--datatype?
--On automatic unsubscription: the receiver channel could respond that it's
--satisfied.

--Circuits are Arrows, having both a source and sink when instantiated.
--MutVars are also sources and sinks... but so is the last value of a stream.
--fixpoint :: Circuit a a -> a?

--Assuming an imperative approach is simplest: need efficient unsubscription.
--That could be achieved with a DLL for O(1) deletion.
--The consumer node should subscribe rather than producer modify, allowing
--self-adjusting computations to be defined all at once.
--self :: M (InChan a)?
--Delta streams have both a delta and state type
--Implement succs => preds using a MapStream k v which can be queried for a
--particular k?
--Adding finality info: Final a is a maximum for each a, but
--Final a > NonFinal b iff a > b.
--(Eq a, Bounded a) => IsMax a where isMax = (== maxBound)
--If you receive a maximum value from any input, you can unsubscribe from it.
--It should be possible to copy an incremental computation graph.

--reachable[f] = any preds[f] reachable
--That needs to subscribe both to function set deltas and bools
--Forwarding any's subscribers to new elems would avoid the intermediate node,
--but passing around InChans is risky.
--A monad with a Finally action could automatically unsubscribe from all inputs,
--but only inchan => outchans is tracked.

--Need to distinguish between return conts, C function roots and intermediate
--BBs.
--fixpoint takes an abstract state map: f=>reachable, args etc; each var
--must be defined in terms of it. Problem: that must be monadic!
--First allocate the outchans and initial values, then concurrently run the
--stream processor initialization.
--That's ~ a read-only monad with an update/send action.
{-
What should the API look like?
chan <- when var (\a -> ...)?
For chans to be able to unsub each other, they need to be allocated before
their final callback is set; they can have a list of callbacks, or just a
Maybe.
Only the init monad should have access to the InChan of the stream.
The Map k (Stream (Set v)) -> M (Map v (Stream (Set k))) needs separate
treatment, as do other multi-output circuits. Preserve the read-only
property.
Unsolved: how to ensure the init monad can't leak its InChans to other nodes
via subscription? Perhaps a st param for each... for now enforce it manually.
TODO formalize why delta streams are fine.
-}

--The abstract interpretation (circuit) monad.
--Uses ST for mutable state.
--The s parameter must be exposed for AI to be able to access the mutable
--references it creates.
--Alternative approaches: STT, ReaderT RunQueue ST
{-
newtype AI s a = AI {runAI :: ConcT (ST s) a}
  deriving (Functor,Applicative,Monad,MonadFix)
instance HasRef (AI s) where
  type Ref (AI s) = STRef
  newRef a = AI $ lift $ newSTRef a
  readRef r = AI $ lift $ readSTRef r
  writeRef r a = AI $ lift $
-}
instance HasRef (ST s) where
  type Ref (ST s) = STRef s
  newRef = newSTRef
  readRef = readSTRef
  writeRef = writeSTRef
--Abstract interpretation monad; its primitive capabilities are exposed via
--the class AIC in order to stack transformers on top of it.
--Since the monads must take an s param it also needs a type family.
--MonadFix is only derived to ensure the tests which demonstrate MonadFix is
--impractical due to deadlock still compile.
newtype AI s a = AI {unAI :: ConcT (ST s) a}
  deriving (Functor,Applicative,Monad,Concurrent,MonadFix)
instance HasRef (AI s) where
  type Ref (AI s) = STRef s
  newRef a = AI $ newRef a
  readRef r = AI $ readRef r
  writeRef r a = AI $ writeRef r a
class Monad m => AIC m where
  type S m
  runCB :: (forall iv . CB iv (S m) a) -> m a
  readChan :: Chan (S m) a -> m a
instance AIC (AI s) where
  type S (AI s) = s
  runCB = unCB
  readChan (Chan rc) = readRef $ rcState rc
--AI is CB with additional internal state; everything AI can do CB iv can as
--well.
instance AIC (CB iv s) where
  type S (CB iv s) = s
  runCB = id
  readChan ch = CB $ readChan ch
--A single instance for transformers.
instance (MonadTrans t, AIC m) => AIC (t m) where
  type S (t m) = S m
  runCB cb = lift $ runCB cb
  readChan = lift . readChan
--Circuit builder; the rigid iv param prevents InChans from escaping.
newtype CB iv s a = CB {unCB :: AI s a}
  deriving (Functor,Applicative,Monad,Concurrent)
--CB may only spawn its own actions, preventing it from mutating external
--state. However, it converts them to AI actions and spawns them to AI's
--runQueue. TODO verify derived Concurrent does that.

--If CB can mutate external STRefs, that breaks its pure-ish property.
--It must therefore be limited to its own internal CBRefs.
--The Chan pattern could be generalized by freezing CBRefs, but for now we
--only need Chans.
newtype CBRef iv s a = CBRef (STRef s a)
instance HasRef (CB iv s) where
  type Ref (CB iv s) = CBRef iv s
  newRef a = CB $ CBRef <$> newRef a
  readRef (CBRef r) = CB $ readRef r
  writeRef (CBRef r) a = CB $ writeRef r a
--outchans <- runCB circuitNode
--runCB :: (forall iv . CB iv s a) -> AI s a
--runCB = unCB
--The raw writeable end of the chan; musn't be allowed to escape.
--No delta handling atm; refine from a working implementation.
data RawChan s a = RawChan {rcState :: STRef s a,
                            rcConsumers :: Consumers s a
                           }
--Consumers should support O(1) subscription and unsubscription; currently
--it's O(log n) and uses Map for simplicity. Note iteration over all
--callbacks is still O(1) per element.
--Each individual subscription must be mutable to be able to refer to and
--cancel other subs.
data Consumers s a = Consumers {
  cSubCtr :: STRef s Int, --It'll never overflow in practice...
  cSubs :: STRef s (IntMap (a -> AI s ()))
  }
--Note the iv parameter in Subscription; you should not be able to leak the
--unsubscription handle, since that would indirectly give external actions the
--ability to affect internal vars.
--The chan rather than Consumers is needed because registered callbacks must
--be spawned once immediately, otherwise wired circuits would never start
--propagating.
data Subscription iv s a = Sub {
  subID :: Int,
  subRC :: RawChan s a
  }
--Wraps the raw chan with the iv
newtype InChan iv s a = InChan (RawChan s a)
--The read-only Chan may escape
newtype Chan s a = Chan (RawChan s a)
--CB actions: alloc new mutable chans, wire them together, then return as
--read-only Chans.
newInChan :: a -> CB iv s (InChan iv s a)
newInChan a = InChan <$> newRawChan a
--Internal.
newRawChan :: a -> CB iv s (RawChan s a)
newRawChan a = RawChan <$> CB (newRef a) <*> newConsumers
newConsumers :: CB iv s (Consumers s a)
--It doesn't actually matter which Int I pick since Int silently overflows.
newConsumers = CB $ Consumers <$> newRef 0 <*> newRef IM.empty
--Creates a cancelable subscription handle; starts with no callback.
subChan :: Chan s a -> CB iv s (Subscription iv s a)
subChan (Chan rc) = do
  let cons = rcConsumers rc
  let ctr = CBRef $ cSubCtr cons
  n <- readRef ctr
  writeRef ctr (n+1)
  return Sub{subID = n, subRC = rc}
--A convenience function that creates a subscription and sets the callback at
--the same time.
subWhenChan :: (a -> CB iv s ()) -> Chan s a -> CB iv s (Subscription iv s a)
subWhenChan f ch = do
  sub <- subChan ch
  whenSub sub f
  return sub
--Sets a callback for a subscription. Can be repeatedly unsub'd and reset,
--but that's bad practice.
--Note this is the one way CB actions with privileged access to the circuit's
--internal chans can escape - they'll later be called from within AI s!
--That's achieved by extracting the internal AI s of CB iv s.
whenSub :: Subscription iv s a -> (a -> CB iv s ()) -> CB iv s ()
whenSub (Sub{subID=id,subRC=rc}) f = do
  let subs = CBRef $ cSubs $ rcConsumers rc
  i2f <- readRef subs
  writeRef subs $ IM.insert id (unCB . f) i2f
  --The callback must be spawned once immediately!
  a <- readRef $ CBRef $ rcState rc
  spawn $ f a
--Deletes the subscription's callback; TODO use helper to share code.
unSub :: Subscription iv s a -> CB iv s ()
unSub (Sub{subID=id,subRC=rc}) = do
  let subs = CBRef $ cSubs $ rcConsumers rc
  i2f <- readRef subs
  writeRef subs $ IM.delete id i2f

--Updates an inChan.
--Needs Eq because subscribers are only notified when the value changes.
writeInChan :: Eq a => InChan iv s a -> a -> CB iv s ()
writeInChan (InChan RawChan{rcState=ra,rcConsumers=rcc}) a = do
  a' <- readRef (CBRef ra)
  if a == a'
    then return ()
    else do
    --Update and notify consumers
    writeRef (CBRef ra) a
    let subs = cSubs rcc
    i2f <- readRef (CBRef subs)
    forM_ (IM.elems i2f) (spawn . CB . ($ a))
--Used when modifying InChans; TODO add classes to share implem between
--monads. IsRef r?
readInChan :: InChan iv s a -> CB iv s a
readInChan (InChan rc) = CB $ readRef $ rcState rc
modInChan :: Eq a => (a -> a) -> InChan iv s a -> CB iv s ()
modInChan f ic = do
  a <- readInChan ic
  writeInChan ic $ f a
--A helper for using modInChan succinctly in circuit combinators
modWith :: Eq a => InChan iv s a -> (a -> a -> a) -> a -> CB iv s ()
modWith ic (+) a = modInChan (+a) ic

--Converts a mutable InChan to a read-only Chan so it can be returned by the
--CB monad.
freezeInChan :: InChan iv s a -> Chan s a
freezeInChan (InChan raw) = Chan raw

--Applications:
--Bounded join-semilattice fold
--When any input becomes top, unsubscribes all inputs.
--Precondition: the chans only increase, minBound is semilattice bottom and
--maxBound semilattice top.
cbOr :: (AIC m, Bounded a, JoinSemilattice a, Eq a) =>
  [Chan (S m) a] -> m (Chan (S m) a)
cbOr cbs = runCB $ do
  ic <- newInChan minBound
  spawn $ do
    subs <- mapM subChan cbs
    forM_ subs $ flip whenSub $
      \a -> do
        modInChan (\/ a) ic
        new <- readInChan ic
        if new == maxBound
          then mapM_ unSub subs
          else return ()
  return $ freeze ic

--invertGraph takes a growing directed graph with nodes k and returns the
--graph with edges reversed. To be used to obtain preds[f] from succs[f].
--Logic: whenever in[f] += g, out[g] += f
--Identifying new g's added requires computing the delta of in[f], requiring
--an additional CBRef per key.
--invertGraph demonstrates the power of the CB model: you can return a
--structure containing many independently updating chans, rather than just
--one.
--S.difference on the successor sets risks getting expensive... TODO
--propagate deltas further.
invertGraph :: Ord k => Map k (Chan s (Set k)) ->
               CB iv s (Map k (Chan s (Set k)))
invertGraph k2chks = do
  --Allocate a map of inchans initialized to be empty
  k2in <- mapM (\_ -> newInChan S.empty) k2chks
  --For each (k,ch) in the input map, subscribe to ch's deltas
  --When k2chks[k] grows by ks, add k to k2in[k'] for each k' in ks
  forM_ (M.toList k2chks)
    (\(k,ch) ->
        subSetDelta
        (\k' -> case M.lookup k' k2in of
                  Nothing -> error "!!?"
                  Just inch -> modInChan (S.insert k) inch)
        ch)
  --Freeze and return the inchans
  return $ freeze k2in
--f => g => label -> g => f => label
invertLabeledGraph :: (Ord k, Eq v) =>
  Map k (Chan s (Map k v)) ->
  CB iv s (Map k (Chan s (Map k v)))
invertLabeledGraph k2chm = do
  k2in <- mapM (\_ -> newInChan M.empty) k2chm
  --When k
  forM_ (M.toList k2chm)
    (\(k,ch) ->
       subMapDelta
       (\k' v -> case M.lookup k' k2in of
                   Nothing -> error "!!?"
                   Just inch -> modInChan (M.insert k v) inch)
       ch)
  return $ freeze k2in
--Allocates a delta tracker and registers it to the given chan.
--Uses a CBRef to track the old value; the initial delta is the current value
--of the Chan.
--Requirement: forall x . x-zero = x
subDelta :: a -> (a -> a -> a) -> (a -> CB iv s ()) ->
  Chan s a -> CB iv s (Subscription iv s a)
subDelta zero (-) callback chan = do
  cbr <- newRef zero
  subWhenChan (\a -> do
                  old <- readRef cbr
                  writeRef cbr a
                  callback $ a - old) chan
--As the input set grows, applies a callback to each new element.
--Q: Is exposing the subscription dangerous?
subSetDelta :: Ord a =>
  (a -> CB iv s ()) ->
  Chan s (Set a) ->
  CB iv s (Subscription iv s (Set a))
subSetDelta callback =
  subDelta S.empty S.difference
  (\delta -> forM_ (S.toList delta) callback)
--Ditto extended to Map; applies a callback for each new k-v mapping.
--Assumption: maps only grow, and their v's never change.
subMapDelta :: Ord k =>
  (k -> v -> CB iv s ()) ->
  Chan s (Map k v) ->
  CB iv s (Subscription iv s (Map k v))
subMapDelta callback =
  subDelta M.empty M.difference
  (\delta -> forM_ (M.toList delta) $ uncurry callback)

--Consider f.lhs = for all callers[f], \/ of args[f].
--Precondition: f.lhs and args[f] match.
--callers[f] is a Chan (Set f), from which you must obtain the [Chan AbVar]
--args[f].
--The forAll is interesting because it requires linking new inputs (args[f]) as
--new fs are added.
--Mapping over the delta set is not desirable, since that would require the
--work of sorting the [Chan AbVar] lists... and there's no Ord instance for
--Chan.
--Solution: S.toList
--'mapping' the set gives me a stream of elements; it extends, but the prefix
--never changes. However, later queries may return existing elements in a
--different order. The operations applied to the stream must therefore be
--commutative... but not idempotent, consider "sum of f of s".
--Streams which enforced that via class constraints on consumers might be
--a good idea.
--Write a specific version first, then extract combinator.
collectVars :: (JoinSemilattice b, HasBottom b, Eq b, Ord a) =>
  Int -> --length of result, >= 0
  Chan s (Set a) ->
  (a -> [Chan s b]) -> --vars associated with a
  CB iv s [Chan s b]
collectVars len chset f =
  forAll (sequence $ replicate len (newInChan bottom)) chset $
  \inchs a -> linkChans (f a) inchs
  {-
  do
  inchs <- sequence $ replicate len (newChan bottom)
  subSetDelta (\a -> linkChans (f a) inchs) chset
  return $ map freezeInChan inchs
-}
--Using the m () ~ an equation view, but now the mutable state being updated
--is kept internal.
forAll :: (Ord a, Freezable state) =>
  CB iv s state ->
  Chan s (Set a) ->
  (state -> a -> CB iv s ()) ->
  CB iv s (Frozen state)
forAll mkSt chset f = do
  st <- mkSt
  subSetDelta (f st) chset
  return $ freeze st
--Generalizing to maps:
forAllMap :: (Ord k, Freezable state) =>
  CB iv s state ->
  Chan s (Map k v) ->
  (state -> k -> v -> CB iv s ()) ->
  CB iv s (Frozen state)
forAllMap mkSt chmap f = do
  st <- mkSt
  subMapDelta (f st) chmap
  return $ freeze st
--Helper function; links a new list of a's to the inchans.
linkChans :: (JoinSemilattice a, Eq a) =>
  [Chan s a] -> [InChan iv s a] -> CB iv s ()
linkChans chans inchans
  | length chans /= length inchans = error "!!?"
  | let = zipWithM_ (\inchan ->
                        subWhenChan (\a -> modInChan (\/ a) inchan))
          inchans chans
--A prettier variant of forAll that handles mapping over new set elements
--and op application; used for reachable[f] = any reachable (preds f).
--Doesn't unsubscribe.
--To do so with minimal code reuse would require a concept of streams in order
--to map convert over the delta stream.
--foldChanStream :: (a -> b -> b) -> b -> Stream s (Chan s a) -> AI s (Chan s b)
setFoldr :: (AIC m, Eq b, Ord c) =>
  (a -> b -> b) -> b -> (c -> Chan (S m) a) -> Chan (S m) (Set c) ->
  m (Chan (S m) b)
setFoldr (+) zero convert chset = runCB $
  forAll (newInChan zero) chset
  (\chb c -> do
      subWhenChan (\a -> modInChan (a+) chb) (convert c)
      return ()
  )
setAny :: (AIC m, Ord a) =>
  (a -> Chan (S m) Bool) -> Chan (S m) (Set a) -> m (Chan (S m) Bool)
setAny = setFoldr (||) False

--When a Boolean chan becomes true (which happens only once), run an action.
--Unsubscribes itself for efficiency. Ignores action return type.
doWhen :: Chan s Bool -> CB iv s a -> CB iv s ()
doWhen bch m = do
  sub <- subChan bch
  whenSub sub (\b -> if b
                     then m >> unSub sub
                     else return ())

--The combinator used for EVM op AI
--Behavior: if any input chan changes, update output chans
--Assumption: the chans and op are monotonic.
--A circuit linking many chans with a single function can be generalized using
--a class with instances for Chan s, Pair, [] etc.
--However,I don't need that just yet.
opAI :: (AIC m, Eq a, HasBottom a) =>
  (Int,Int) -> --The return arity of the op; arg arity is implicit in input
  (([a],[a]) -> ([a],[a])) -> --The op behavior
  ([Chan (S m) a],[Chan (S m) a]) -> --The input AbVar chans
  m ([Chan (S m) a],[Chan (S m) a])
opAI (wlen,slen) f (wchs,schs) = runCB $ do
  --Initial state
  wins <- replicateM wlen $ newInChan bottom
  sins <- replicateM slen $ newInChan bottom
  let callback = do
        --Read every chan, apply f to get output values, write to inchans
        ws <- mapM readChan wchs
        ss <- mapM readChan schs
        let (outws,outss) = f (ws,ss)
        zipWithM_ writeInChan wins ws
        zipWithM_ writeInChan sins ss
  mapM_ (subWhenChan (const callback)) (wchs++schs)
  return $ freeze (wins,sins)
         
--reachable[f] = any preds[f] reachable
--That can be implemented using forAll 1, but it would be better to
--pass the init action CB iv s st as a param in forAll.
--TODO a Freezable class and Frozen tyfam, enabling freezing of multi-chan
--containers with a single function.
class Freezable a where
  type Frozen a
  freeze :: a -> Frozen a
instance Freezable (InChan iv s a) where
  type Frozen (InChan iv s a) = Chan s a
  freeze = freezeInChan
instance Freezable a => Freezable [a] where
  type Frozen [a] = [Frozen a]
  freeze = map freeze
instance Freezable a => Freezable (Map k a) where
  type Frozen (Map k a) = Map k (Frozen a)
  freeze = M.map freeze
instance (Freezable a, Freezable b) => Freezable (a,b) where
  type Frozen (a,b) = (Frozen a, Frozen b)
  freeze (a,b) = (freeze a, freeze b)
{-
--The instance I'd like to write
instance Functor f => Freezable (f a) where
  type Frozen (f a) = f (Frozen a)
  freeze = fmap freeze
-}

--Apply f to a Chan, unsubscribing when f x becomes max.
--Invariant: f is monotonic.
--Useful for "jumpi cond may be false/true"
mapChan :: (Eq b, HasTop b) => (a -> b) -> Chan s a -> CB iv s (Chan s b)
mapChan f ch = do
  b <- f <$> readChan ch
  inch <- newInChan b
  sub <- subChan ch
  whenSub sub (\a -> do
                  let b = f a
                  if b == top
                    then unSub sub
                    else return ()
                  writeInChan inch b)
  return $ freeze inch

--State s a ~ s -> (a,s).
--To prevent an infinite runQueue, the equation needs to start by
--setting runQueue to []? Apparently not!
--To prevent deadlock, need to ensure ModState structure depends only on
--Core and that no Chan is evaluated before completion; all effects other
--than newInChan and spawn must be deferred?
--That means mapChan is invalid: inChans must be given an initial value before
--the Chans they depend on are read.
--readChan is still needed in CB, since the op circuit (reeval on any arg
--changed) needs it.
--Subscription (which forces the chans when it modifies them) must be
--deferred.
--TODO make a simple test of mfix and Chan propagation (propagation of or
--through a Boolean circuit).
--Simpler: create a Chan, spawn a write to it.

--Nulls the runQueue first.
--myfix :: (a -> AI s a) -> AI s a
--myfix f = mfix (\a -> {-ConcT (put []) >> -} f a)

runAI :: (forall s . AI s a) -> a
runAI ai = runST $ runConcT $ unAI ai
test_1 :: Bool
test_1 = runAI $ do
  ch <- mfix (\_ -> runCB $ do
                  inch <- newInChan False
                  spawn $ writeInChan inch True
                  spawn $ error "Woo!"
                  return $ freeze inch
              )
  len <- length <$> AI (ConcT get)
  --error $ "runQueue length: " ++ show len
  scheduler
  readChan ch

--x = x || True
--cbOr deadlocks... spawning subscription and reading fixed it.
test_2 = runAI $ do
  ch <- mfix (\x -> do
                 true <- runCB $ freeze <$> newInChan True
                 cbOr [x,true]
             )
  scheduler
  readChan ch

--Accessing chans from within a structure
--Consequence: deadlock.
test_3 = runAI $ do
  chs <- mfix (\[x,y,z] -> do
                  true <- runCB $ freeze <$> newInChan True
                  --mapM (\v -> cbOr [v,true]) [x,y,z]
                  x' <- cbOr [x,true]
                  y' <- cbOr [y,true]
                  z' <- cbOr [z,true]
                  return [x',y',z']
              )
  --scheduler
  mapM readChan chs

--Solution: don't rely on mfix. Instead alloc knot-tying chans,
--build the circuit based on them and then wire the output back to them
--(breaking the abstraction).
--unsafeWire :: UnsafeWire a => a -> a -> AI s ()
{-
class UnsafeWire a where
  type UWS a :: Type
  unsafeWire :: a -> a -> AI s ()
instance UnsafeWire (Chan s a) where
  type UWS (Chan s a) = s
-}
unsafeWire :: (AIC m, Eq a, JoinSemilattice a) =>
  Chan (S m) a -> Chan (S m) a -> m ()
unsafeWire from (Chan to) = runCB $ do
  subWhenChan (modWith (InChan to) (\/)) from
  return ()

test_4 :: [Bool]
test_4 = runAI $ do
  xyz <- mapM newChan [False,False,False]
  let [x,y,z] = xyz
  xyz' <- do
    true <- newChan True
    --This will require multiple iterations
    x' <- cbOr [x,true]
    y' <- cbOr [y,x]
    z' <- cbOr [z,y]
    return [x',y',z']
  zipWithM_ unsafeWire xyz' xyz
  scheduler
  mapM readChan xyz

--A chan with no subscriptions and a constant value... until you unsafeWire it.
newChan :: AIC m => a -> m (Chan (S m) a)
newChan a = runCB $ freeze <$> newInChan a

--Unsafely wiring the circuit output to the knot-tying value is the one point
--where the abstraction breaks.
--How to allow the user to tell fixpoint how to wire an a to an a for new
--chan-containing types a without letting them do so directly?
--Ideally breaking the abstraction should not be possible from within Safe
--Haskell (as long as only a safe API is exported).
--Idea: let the user specify how to pair the chans in a1 with those in a2
--(where a1 and a2 have the same shape and may contain multiple chan types)
--using a class Weldable a where weld :: a -> a -> Fuse s.
--Fuse is a monoid with a single action
--fuse :: Chan s a -> Chan s a -> Fuse s
--that wraps an unsafeWire.
--fixpoint :: (Weldable a, HasInitialState a) =>
-- (a -> AI s a) ->
-- AI s a
--is then the only function permitted to unwrap Fuse.
  
--Chans are useful for incrementalizing computation, but it would still be nice
--to have streams in order to conveniently apply fmap, (<*>) etc.
--By stream I mean an event source.
--Stream a ~ (a -> CB iv s ()) -> CB iv s ()?
--subChan :: Chan a -> Stream a
--Streams (or the stream head produced by running it) should also be
--queryable to enable (<*>) to be implemented. That requires an additional
--CBRef.
--To share a stream output, you'd need to add subscription...

--A Chan has two ends, InChan and (out)Chan. InChans are only used internally
--by circuit combinators.
--Combinators: Map k (Chan s (Set k)) -> AI s (Map k (Chan s (Set k)))
--It can't be Map k (... (Set v)) because the shape of the map must be known
--at creation time; the keys of the output are the same as the input.

--InChan can be written to
--subscribe :: Chan s a -> AI s (Subscription s a)
--when :: Subscription s a -> (a -> AI s ()) -> AI s ()
--unsubscribe :: Subscription s a -> AI s ()

--Receiving the module abstract state as a pure value via mfix means you
--can use a pure fun to look up new f in preds => f.passes
--Chan (Set f) -> (f -> Chan a) -> AI s (Chan a)
--type CircuitBuilder iv s a
--runCB :: forall iv . CB iv s a -> AI s a
--Can spawn Chan s a, InChan iv s a
--Can register callbacks :: b -> CB iv s (), which are converted to
--AI s (); that is the only way to convert.
--Invariant: the value of internal state depends only on inchans.
--Sufficient for termination:
--1) Each circuit implements a function f
--s.t. ins =: x => outs = f x after change propagation settles.
--2) f is monotonic with the finite ascending chain property.
--Termination is not necessary for (Haskell's concept of) purity.
--Note a circuit is self-contained once constructed.
--If you recorded more dependency info it should be possible for queries on
--circuits to terminate even when part of the circuit diverges, e.g.
--"select these outvals" or "outval >= k?".
--Chan/Var updates are analogous to thunk evaluation; subscribing to a var
--of a running circuit could be pure.
