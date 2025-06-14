module TypeCheck.PatternDecomposition where

{-Pattern combinators after global => *global substitution, converting each
Con args to use explicit fields:
_, local, p.field, p[ix], UBCon {field: p}, BCon {field: p}, *e, e[e]

Problem: indexing may be applied either to arrays or ptrs.

Decomposition:
p = e =>
let x = e
caseE x of
 p -> x
Tricky problem: composite patterns can't just match from left to right because
later ones may fail! Side-effecting matches (*ptr, local) may not be applied
until the pattern is infallible.

Con {field: p} = e where Con is the only constructor in the type:
let x = e
    p = x.field
in x
Otherwise it's transformed to
let x = e
caseE x of
 Con {field: p} -> x
Every unboxed multi-con datatype with params needs an enum datatype and a
function to extract the tag. Enum datatypes don't; they're their own tags.

case e of
 BoxedCon1 {field: p} -> cont;
 BoxedCon2 {...} -> ... =>
Look up DT of all cons; if they're not the same you can error immediately
Look up TagDT of DT and StructDT for each BoxedCon
StructDT structure: tagDT, fields
let x = e
    pr = regionOf x :: ProxyRegion r
case coerce x :: Ptr r TagDT of
 TagCon1 ->
  let ptr = coerce x :: Ptr r StructCon1
      StructCon1 {field' : p} = *ptr
  in cont;
 ...
Note: tags may be assumed to remain constant

coerceRegion :: ProxyRegion r -> a -> Ptr r t
-}
