module GlobalLayout (globalLayout,LayoutError(..)) where

import AST.DTs (Module(..),Region(..),Name(..))
import AST.Util (rollTyApps)
import Mono.Mono (MonoS(..))
import Sizeof (Sizeof(..),sizeofT)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State

--Fixes the offsets of non-Code globals, i.e. Memory, Storage and TStorage.
--For each region, they're laid out contiguously in lexicographic order,
--starting at offset 0; todo allow the user to specify layout per region.
--Example: a : Short; memory a; b : Byte; memory b; c : Short; memory c =>
--a @ 0, b @ 2, c @ 3, memOffset = 5
--Potential future opt: add padding to prevent storage and tstorage globals
--from overlapping words when possible. That's a nontrivial choice since
--it may increase the cost of loading all globals.
--TODO figure out how to interleave global placement with Core optimization:
--Core opts can eliminate uses of globals, but there's a cyclical dependency
--between global layout and Core behavior.
--Code globals are laid out after bytecode generation, since data must be
--placed after text.
--Globals reduce to 16b byte-addressed pointers; layout fails if the globals
--of any region take up more than 2^16 bytes.
--The *Offset globals are always placed last if they're present; their
--absence does not trigger an error.

--TODO present the already placed globals of the offending region in order.
data LayoutError = AddressSpaceExhausted Region
  deriving (Eq,Ord,Read,Show)
data Layout = Layout {globalOffsets :: Map Name Integer,
                      regionOffsets :: Map Region Integer
                     }
  deriving (Eq,Ord,Read,Show)
globalLayout :: Module -> MonoS -> Sizeof ->
  Either LayoutError (Map Name Integer)
globalLayout mod monoS sizeof = do
  let gs = reorder $ exploredGlobals monoS
  globalOffsets <$> execStateT (mapM_ push gs) Layout{globalOffsets=M.empty,
                                                      regionOffsets=
                                                         M.fromList [(Me,0),
                                                                     (St,0),
                                                                     (TS,0)
                                                                    ]
                                                     }
  where
    offsets = S.fromList $ map (++"Offset") $ words "mem sto tsto"
    --Places the *Offset vars last
    reorder :: Set Name -> [Name]
    reorder gs = S.toList (S.difference gs offsets) ++
                 (S.toList offsets) >>= yank
      where yank nm = [nm | nm `elem` gs]
    push :: Name -> StateT Layout (Either LayoutError) ()
    push g =
      case M.lookup g $ globals mod of
        Nothing -> error "This won't happen"
        Just (r,me) -> do
          Layout{globalOffsets = go,
                 regionOffsets = ro
                } <- get
          case M.lookup r ro of
            Nothing -> return () --It's a code global
            Just off ->
              case M.lookup g $ tysigs mod of
                Just ([],monoT)
                  | Just sz <- sizeofT sizeof monoT -> do
                    let newOff = off + sz
                    if newOff > 65535
                      then lift $ Left $ AddressSpaceExhausted r
                      else put Layout{globalOffsets = M.insert g off go,
                                      regionOffsets = M.insert r newOff ro
                                     }
                _ -> error "This won't happen either"
