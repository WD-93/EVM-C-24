module Desugar.Util where

--Widely used functions which have no particular place; could also be called
--Misc

import AST.DTs (Name(..))

--If a constructor is defined as Con args rather than Con {field: t}, it's
--given the fields defaultFieldName "Con" 1..arity
defaultFieldName :: Name -> Int -> Name
defaultFieldName con ix
  | ix < 1 = error $ "Badarg to defaultFieldName: " ++ show ix
  | let = "field" ++ con ++ show ix
