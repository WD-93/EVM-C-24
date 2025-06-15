module Desugar.Constructors where

--Desugars Con args patterns to Con {field: p}
--Con {field: e} exprs desugar to let x = e in Con x. Duplicate fields are
--allowed in patterns, but disallowed in exprs.
--Note a [(Name,E)] is required because the ordering of field: e determines
--eval order. Ordering also matters for patterns because they may contain
--side-effecting exprs!
--If Con args is overapplied, the first n arguments are included in the Con app,
--where n is Con's arity. That makes it possible (but perhaps not desirable)
--to represent (->) using data Fun a b = {MkFun (UInt 2)}.
--TODO: change Int len param to byte size so I don't need type-level /8.
--For now, disallow underapplied constructors.

--Step 1: for each non-record ConDecl Con ts, allocate fields .field$Con<N>
--with the appropriate fieldType and fieldSpec; replace the ConDecl with a
--record ConDecl.
--Note Desugar.Desugar enforces the precondition that there are no conflicting
--con decls.
--The constructor types are available in constructors
fillInMissingFields :: Module -> Module
fillInMissingFields m = undefined
  where
    ds = datatypes m
    cs = constructors m
    (ds',field2t,field2spec) = go M.empty M.empty M.empty $
                               M.toList ds
    go ds' field2t field2spec = \case
      [] -> (ds',field2t,field2spec)
      (tycon,(args,condecls)):rest ->
        --let condecls' = desugar condecls
        undefined
--Then convert PConArgs con ps to PCon and Var con :$ ...args to
--ConRecord con argsPrefix :$ ...argsSuffix
