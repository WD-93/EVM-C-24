{-# LANGUAGE LambdaCase #-}
module IR.DTs where

import Data.Map(Map(..))

import AST.DTs
--Splitting out the DTs defined in IR to allow Pretty to access them;
--TODO define Show instances in Pretty.
--Since the IR modules are going in their own folder, it does not make sense
--to put CFG datatypes here...

--Function call is treated as an op.
--Standard arg order for Call: $mem,$sto,$tsto,$ext,args,$ret
data IRT = Mem  --has no runtime repr
         | Sto  --represents the storage state
         | TSto --ditto for tstorage
         | Ext  --represents the state of external contracts
         | W Int T --nth word of C-level t; 1-indexed
         --Renamed from Word to avoid clash with Padding
  deriving (Eq,Ord,Read,Show)
--Returns true if the IRT has no runtime repr because it represents state;
--to be used in later stages.
isVirtual :: IRT -> Bool
isVirtual = \case
  W{} -> False
  _ -> True

--Name mangling: nth word of local x becomes x#n
--From ToyCFG: IR is tagged with () or Live annots.
--It does not need a var type param because SSA is done on CFG's.
data IRP a = Op a [(Name,IRT)] Operator [Name]
               | Ifte a Name [IRP a] [IRP a]
               | While a [IRP a] Name [IRP a]
               | DoWhile a [IRP a] [IRP a] Name --body, cond
               | Return a [Name]
               | Break a Int
               | Continue a Int
               | TailCall a Name [Name]
               | IRComment String --Ignored in later stages, used for debugging
               --Branching EVM instructions
               | EVM_RETURN a Name Name Name Name Name Name
               -- $mem, $sto, $tsto, $ext, ptr, len
               --For case:
               --switch tag numTags cases
               --Only cases for tags in the range 0..numTags-1 are acceptable.
               --If the tag (a 1-byte value) has no matching case, revert with
               --no message.
               --Naive compilation: if numTags is not a power of two, and it
               --by its bitlen and add revert cases directly to the jump table.
               --If it is 2^n < 256, add an if tag > 2^n then revert() first.
               --If numTags == 256, simply make a 256-elem table.
               --Note switch is a bit of a misleading name; it doesn't do
               --fallthrough like C switch
               | Switch a Name Int (Map Int [IRP a])
  deriving (Eq,Ord,Read,Show)
type IR = IRP ()

data Operator = Push StaticValue
              | Opcode String
              | Call --args: mem,sto,tsto,ext,f,args,ret
              | Reduce Name --arg: a commutative and associative opcode,
                --used for truthy
              | Copy --x = y => x = copy [y]
  deriving (Eq,Ord,Read,Show)
--Ret and f are created by push staticValue
data StaticValue = Const Integer
                 | LabelConst Name
  deriving (Eq,Ord,Read,Show)

--Top-level function: given a module, generates the IR for each function.
--Pruning based on actual calls made from main can be done later.
--FW problem: the IR output may need additional info for placement, such as
--whether the code is a library, exported functions and JTs
data IRModule = IRM {
  irDefuns :: Map Name (Arity,[IR]),
  --Static data: strings, arrays, nested modules
  --For now, just strings
  --(Name,Int) is a label use, Int a byte
  --C-allocated anon label format: fname.static#n
  --That ensures the counter needn't be shared between function compilations
  staticData :: Map Name Static
  }
  deriving (Eq,Ord,Read,Show)
--Not very storage-efficient for strings...
type Static = (T,[Either (Name,Int) Int])
--The number of argument words a function takes beyond $ret; needed for asm
--generation.
type Arity = Int
