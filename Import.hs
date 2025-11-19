module Import where

import E.Abs
import AST.DTs (Name(..))
import DeclBucket
import Parse (parseModule)
import Util --Errors

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S

--Handles the module system.
--EVMC programs are divided into modules, each of which is in a separate .evmc
--file.
--Modules are parsed into a list of CST decls, which are then split into
--atomic decls and then merged into a DeclBucket.
sourceToBucket :: ModName -> String -> Either String --parse error
                  DeclBucket
sourceToBucket mnm str = do
  Module _loc ds <- parseModule str
  let
    lds = map (addModName mnm) ds
    ads = lds >>= declToADecls
    dbs = map adeclToBucket ads
    db = foldr unionBucket emptyBucket dbs
  return db
--Every module has a unique name Foo.Bar.Baz; a mapping from module names to
--DeclBuckets forms a Namespace.
type Namespace = Map ModName DeclBucket
--The IO phase of compilation collects relevant .evmc files into a namespace;
--the rest of the pipeline is pure.
--Given a namespace NS and a main module M, the dependencies of M (including
--M itself) are determined by the transitive closure of imports.
--If an imported module M' is not in the namespace, compilation fails;
--duplicate imports are a noop.
--The dependencies ms are then merged into a single DeclBucket, which is then
--checked for conflicting definitions.
--Precondition: M is in the namespace; we throw an error without location
--info earlier if the main module is missing.
dependencies :: Namespace -> ModName ->
                Errors (Located ModName) --missing imports
                (Set ModName)
dependencies ns mnm =
  case M.lookup mnm ns of
    Nothing -> error "Precondition violated!"
    Just db -> go (S.singleton mnm) db
      where go = error "todo"
