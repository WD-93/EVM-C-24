{-# LANGUAGE PatternSynonyms, LambdaCase #-}
module Core.Core where

import qualified AST.DTs as E --as in EVMC
import AST.DTs (T(..),Name(..),Module(..),pattern (:->),pattern UInt,tupleT)
import AST.Util (freeVarsPatList)
import Core.DTs
import Mono.Mono (MonoS(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

--Converts a monomorphized EVMC module to a Core lambda
core :: (Module,MonoS) -> Either CoreError Expr
core = error "todo"

--The ways Core conversion can go wrong
data CoreError = BreakOutsideLoop
               | ContinueOutsideLoop
               | UnsupportedFunLHS E.Pat
  deriving (Eq,Ord,Read,Show)

--Algo:
--No support for globals or alloc yet.
--No effects whatsoever except stop() and revert.
--Output:
--letrec
-- cprims = ... --inlinable defs using Core prims
-- coreFs = \(($arg,$ret),<env>) -> ...
--in \(es,sto,tsto,cd) -> main ((),stop)

--For each C function f@ts : T; f p := s, produce a Core function to put into
--the letrec map.
--Each f@ts in C becomes fromFun# f@ts in Core. f x uses toFun# to extract
--the actual Core function. toFun# (fromFun# f) ~ f.
coreF :: (Name,[T]) ->   --unambiguous function name
         T ->            --function type
         E.Pat ->          --lhs
         E.S ->            --body
         CoreM (Id,Expr) --letrec binding
coreF fts t p s =
  --If t is not a -> b, something's gone terribly wrong
  case t of
    a :-> b -> do
      let coreF = coreFunName fts a b
      lam <- coreDefun p s b
      return (coreF,lam)
    _ -> error $ "Compiler error before Core: the function " ++ show (fst fts)
      ++ " has non-function type " ++ show t ++ "!?"
--Only supports var | tuple function LHSes; TODO transform f generalPat into
--f $arg := {generalPat = $arg; ...} in C.
--Convention: local x with version n => x.n
--All vars in the lhs start with version 1.
--TODO handle repeated vars in tuples correctly.
coreDefun :: E.Pat -> --lhs
             E.S ->   --body
             T ->     --return type (needed for return null() cont)
             CoreM Expr
coreDefun p s rett = do
  coreP <- cpat2corepat p
  --The extracted argument vars to be passed to the body
  let coreVs = freeVarsCorePat coreP
  --Until the next shadowing var x = e, each x from the LHS refers to x.1
  --Need to map to the Core vars as well to get the T
  let cvs = freeVarsPatList p
      verMap = M.fromList $ zip cvs $ zip (repeat 1) coreVs
  let returnNull = Lam (coreLHS coreVs rett) $
        App (Var $ Mono "$ret" (rett :-># end)) (PrimFun "null#" [rett])
  coreBody coreVs verMap [s] returnNull

--The LHS of every Core-compiled statement with anonymous expr vars
--eN:tN..e1:t1, locals and return type rett
coreLHS coreVs rett = tuplePCore [tuplePCore $ map PVar $ coreVs ++
                                  [(Mono "$ret" (rett :-># end))],
                                  env]

--var x = e:t effect: scope -> Pair x.n:t scope
--S effect: scope -> scope
--next: b -> End, where b is (scope,env)
--The type of the scope lhs needs to be tracked in order to know how many words
--need to be popped.
--The scope at the end of a block is unknown until it's been traversed.
--That creates a problem: the CPS expr for the block needs a next, but next's
--LHS depends on the block.
coreBody :: [Id] -> --The scope of Core locals on stack
            Map Name (Int,Id) -> --The mapping from C locals to them
            [E.S] -> --The remainder of the block
            Expr -> --the next continuation
            CoreM Expr
coreBody scope verMap s next = 
  error "todo"

--scope = eN,e(N-1)..e1 ... locals
--next takes e(N+1):T,eN..e1...scope. However, T isn't known in advance, so
--the definition of next can't be either! Solution: next is a fresh Name, given
--a T by coreE itself. coreE then reports back the T so the next can be
--letrec-defined.
--eDepth must be recorded to give the right scope to subexpr conts
coreE scope eDepth verMap rett e next = do
  let lhs = coreLHS scope rett
      elhs = corePat2Expr lhs
  (body,t) <- case e of
            E.EInteger n -> do
              v <- freshVarT "$n" $ UInt 32
              return $
                (Let (PVar v) (Lit n) $
                 App next $ pushStack (Var v) elhs,
                 UInt 32)
            --nm is either a local or a global
            --If it's a global, just push it as a Var; it's in scope since
            --it's been letrec-bound.
            --If it's a local, look it up in verMap and push that.
            E.TypedVar (Just t) nm -> do
              (mod,_mono) <- ask
              if M.member nm $ globals mod
                then return (App next $ pushStack (Var $ Mono nm t) elhs, t)
                else case M.lookup nm verMap of
                       Just (_ver,id) ->
                         return (App next $ pushStack (Var id) elhs,
                                  let Mono _ t = id in t)
                       Nothing -> error "Compiler error: This shouldn't happen!"
            --Now the scope must be adjusted using eDepth...
            --f => x => app => mkCont next scope
            --f returns a Fun which must be converted to a CoreFun
            --Oh no: f's type must be known to produce the scope of next,
            --but the cont hasn't been computed at that point!
            --Solution: a letrec. But for the cont to be bound to an id its
            --type must be known!
            f E.:$ x ->
  return (Lam lhs body,t)

--Given a scope vs with e depth ed, produces (e(ed+1):t...scope,ed+1)
incScopeDepth :: [Id] -> Int -> T -> ([Id],Int)
incScopeDepth scope ed t = (Mono ("$e" ++ show (ed+1)) t : scope,ed+1)
--Assuming an expr has pushed n subexprs to stack, fetches the Id of 0-indexed
--subexpr args[m].
--Example: scope = eN:t,..., n = 2, m = 1 => result = eN
getNthArg :: [Id] -> Int -> Int -> Id
getNthArg scope n m
  | m >= n = error "Compiler error: getNthArg"
  | otherwise =
    let rev_args = take n scope
    in reverse rev_args !! m

--Given (stack,env), pushes v to stack
--It's a syntactic transformation, assuming its Expr argument is an explicit
--tuple.
pushStack v (EPair stk rest) = EPair (EPair v stk) rest
corePat2Expr :: P -> Expr
corePat2Expr = go
  where go = \case
          PVar v -> Var v
          PUnit -> EUnit
          PPair a b -> EPair (go a) (go b)
  
--Converts a C pattern to a Core pattern iff the C pattern is of form
--p ::= x | tuple [p].
--Core Pair pattern constructors don't need to be type-tagged, since the
--elements are anyway.
--Wildcards are replaced with newly allocated Ids here, so it needs to be in
--Core.
cpat2corepat :: E.Pat -> CoreM P
cpat2corepat = go
  where go = \case
          E.PWild (Just t) -> do
            v <- freshVar "$anon"
            return $ PVar $ Mono v t
          E.TypedPVar (Just t) v ->
            return $ PVar $ Mono (v ++ ".1") t
          E.PConArgs "Unit" (Just []) [] -> return PUnit
          E.PConArgs "Pair" (Just [_a,_b]) [a,b] -> do
            pa <- go a
            pb <- go b
            return $ PPair pa pb
          p -> throwError $ UnsupportedFunLHS p
freeVarsCorePat :: P -> [Id]
freeVarsCorePat = go
  where go = \case
          PVar id -> [id]
          PUnit -> []
          PPair a b -> go a ++ go b

freshVar :: Name -> CoreM Name
freshVar nm = do
  s <- get
  let n = nameCtr s
  put s{nameCtr = n + 1}
  return $ nm ++ show n
freshVarT :: Name -> T -> CoreM Id
freshVarT nm t = flip Mono t <$> freshVar nm
  

coreFunName :: (Name,[T]) -> --unambiguous function name
               T ->          --argument type
               T ->          --return type
               Id            --the corresponding Core function's name
coreFunName fts a b = Poly fts $ coreFunType a b
--The Core function type a Fun a b gets converted to:
coreFunType a b = tupleT [
  tupleT [a, --argument
          tupleT [b,evmState] :-># end] --return cont
  , evmState
  ] :-># end

--The Core compilation monad.
--Needs a counter for allocating fresh names and to throw CoreError
--It also needs Reader access to Module and MonoS
--Associating C locals with version (to avoid confusion due
--to shadowing) is simpler to do via explicit arg passing.
--TODO make an AllocInt m class so I can reuse the name alloc functions across
--monads?
type CoreM = ReaderT CoreR (StateT CoreS (Except CoreError))
type CoreR = (Module,MonoS)
data CoreS = CoreS {nameCtr :: Int}
  deriving (Eq,Ord,Read,Show)
-- ***************************Old comments*************************************
--A statement is well-behaved iff it contains no non-local control flow:
--break or continue.
--Halting exprs are OK; a well-behaved while becomes
--(scope',s') <- f (scope,s)
--The same is true for ifte.
--break => Return# (scope',s'), continue => f (scope',s'),
--where f is the last enclosing while loop and scope' fits it.
{-Ex where scope is different in different loops:
var x = 10;
while (x--) {
 var y = 10;
 while (y--) x--;
}
-}
--Break and continue necessitate CoreError, since occurring outside a loop is
--malformed.

--Every subexpr becomes
--x <- e
--Add a Bind constructor to speed up rewrites?
--Return# a >>= f = f a
--Revert# bs >>= _ = Revert# bs --etc

--Now EVMC primfuns must be given explicit definitions in terms of Core
--primfuns.
--They're computed from the given type params; a failing lookup shouldn't
--always throw an error, as dynamically sized values (FW) lack a sizeof but
--can support dynSizeof.
-- *dsp1 = *dsp2 can use dynSizeof instead of sizeof.

--times a b has a different shape depending on signedness;
--FW: incrementally move such overloading to Prim.evmc
