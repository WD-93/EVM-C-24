module Fused where

--Monomorphization, structured IR generation, datatype sizeof calculation,
--const serialization and global layout interleaved in one phase.
--Simple solution: a RWSE monad
type FusedM = ReaderT Module (
  WriterT [Structured] (
      StateT FusedS (
          Except FusedError
          )
      )
  )
data FusedS = FS {
  --To prevent infinite loops in recursive funs
  fsVisitedFuns :: Set (Name,[T]),
  fsDefuns :: Map (Name,[T]) [Structured],
  --To prevent infinite loops in code g = <e that depends on g>
  fsVisitedGlobals :: Set Name,
  --Code global g => label g(offset: 0, len: 2) : Ptr Code t
  --other g => off : Ptr r t
  --The code global's initializer is also included.
  fsGlobals :: Map Name (Either (T,Const) (Region,T,Integer)),
  --Datatypes:
  fsVisitedDatatypes :: Set MonoT,
  --We currently don't record internal padding
  fsSizeof :: Map MonoT Integer,
  --Monomorphized E recorded for symbolic opts
  fsTags :: Map (Name,[T]) (E,Const), --Con@ts => tag
  fsOffsets :: Map (Name,[T]) Integer --field@ts => off for UBCons
  }
  deriving (Eq,Ord,Read,Show)

--Typechecked module =>
--f@ts => structured IR
--non-code g => offset
--code g => serialization
--monoT => sizeof
--con => serialized tag
--field => offset
--Incrementally cache DT info, recomputing Append, WordPad, Int, Ptr rather
--than caching them (?)
--I'll include type annots in Vars as before; they're required to distinguish
--State vars from words.

--First, find params for main that yield () -> ().
--If main does not exist, error.
--If no such params exist, error.

--Given an f@monoTs:
--Substitute tyvar[i] for monoTs[i].
--Generate structured IR:
--Get wordcount of argument, initial scope = $arg1..$argN,$ret
--Declare lhs vars; match lhs with $arg; scope = lhs vars.
--Generate the given stmt.
--SE e => vs <- generate e
--Return e => vs <- generate e; emit $ Return $ret:vs
--Ifte e th el => w <- generate (truthy e); sth <- isolate th; sel <- isolate el
-- emit $ Ifte w sth sel
--While similar, except e is isolated
--Case e cases => vs <- e; compileCase cases vs
--Case is complex: patterns may be fallible or infallible, boxed or unboxed,
--tag scheme varies. Drop all cases after the first infallible one.
--No infallible case => revert as default
--Otherwise => infallible case as default
--Only one case: equivalent to block
--Core needs in-code JT support for N1.
--Block: trivial
--Break, continue: trivial
--Declare v_es: why do the vars not include type...?

--Lookup special compilation schemes for primfuns: Map Name ([T] -> m ...)

--E:
--k: pushK k
--g: explore g >>= push
-- Non-code g becomes a push0,1 or 2; code gs become a push2 label
--addressOf *e: special case
--f :$ x => vf <- go f; vsx <- go x; emit $ Call vf vsx
--p := e => vs <- go e; assign p vs;
--EArray: eval all subexprs in order, concatenate them
--f@ts: explore f@ts >>= push
--caseE => don't support yet...
--p += k => vs <- eval p, p(vs) = k + p(vs)
--(++) etc: similar
--WordPad@[a] {unWordPad: e}: copy
--Con@ts fs => explore TyCon ts, eval fields in textual order, concat,
--prepend tag if any.
--e.field: look up sizeof e, offset and size of field, slice.
--Slice opts: data is leftmost excluding padding or rightmost.

--Patterns containing es must be evaluated on assignment. In non-default cases
--the top-level tag check is omitted.
--Assign: vs => ()
--_ = vs => pass
--local => copy op --omit copy in Core?
-- *p = vs => writePtr p vs --Convert (*p).field* => *p' first
--Define an indexArrayPtr primitive for PBang?
--Pointer overflows or underflows are UB, creating corrupt values on stack.
--PArray trivial; PCon may require tag check
--PDot requires unfolding, special treatment of unWordPad.

--Explore g: if const in cache, return it
--If non-code: set to current region offset, bump region offset by sz
--If code: serialize initializer, return label
--Don't support allocValue in serialize for now.

--Explore DT@ts: special-case WordPad.
--Serialize tags per con if any
--Compute sizeof + offsets per field
--Allow g, &(p->field)... and *codeG?
--Need to support indexPtr, offsetPtr. Allow label+k in consts?
