module OpcodeInfo where

import Prelude hiding (reads) --I use the name to describe side effects

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S

--All the information about opcodes relevant to compilation.
--EVMC.evmc could be generated from it.
--I could also generate a datatype for opcodes.
--Fused needs: arg and ret arity, effects for state var lhs, rhs in emit.
--Opt needs: gas cost
--Stack needs: effects for ordering instructions.
--TODO deduplicate with Opcodes (which just maps mnemonic to opcode), add
--richer effect and gas cost info (exact range modified, gas cost as a function
--of EVM state).
--Op types: ordinary ws -> w | () with effects
--calls fit under that umbrella
--push* --the only ops with imm args, always returns word
--jumpdest --noop, jumps must be to a jumpdest
--dup,swap,pop --never used in Core
--Branching instrs:
--stop --sto,tsto,ext
--return --mem,sto,tsto,ext
--revert --mem
--invalid --none
--jump, jumpi --branches, consumes whatever the dest | else case does.
--jumpi is special in that 

data OpcodeInfo = OI {
  oiOpcode :: Int,
  oiMinGas :: Int, --simplification: we use min gas when optimizing
  oiArgArity :: Int, --stack words popped
  oiBehavior :: OpcodeBehavior
  }
  deriving (Eq,Ord,Read,Show)
data OpcodeBehavior =
  --The only op type allowed in Core let-bindings.
  --Convention: return output states in S.fromList order.
  Normal {obReturns :: Bool, --0 or 1 words
          obEffect :: Effect
         }
  | Push Int --has n bytes of imm arg, always returns 1 word
  | Dup Int --1..16, doesn't fit in Core's model
  | Swap Int --1..16, doesn't fit in Core's model
  | Pop --pointless in Core since it has no outputs and Stack inserts pops
  --Branching ops consume all their state since control is transferred.
  | Branching {obEffect :: Effect}
  deriving (Eq,Ord,Read,Show)
data Usage = Borrows | Consumes --an op never does both to the same resource
  deriving (Eq,Ord,Read,Show)
data Effect = Effect {effInputs :: Map State Usage,
                      effOutputs :: Set State
                     }
  deriving (Eq,Ord,Read,Show)
--Sugar for describing effects; trying to input or output the same state twice
--is a compiler error.
(&) :: Effect -> Effect -> Effect
e1 & e2 =
  let inKs = M.keysSet . effInputs
      conflictIn = S.intersection (inKs e1) (inKs e2)
      conflictOut = S.intersection (effOutputs e1) (effOutputs e2)
  in case () of
       _ | not $ S.null conflictIn ->
           error $ "Compiler error: conflicting inputs in " ++ show (e1,e2)
         | not $ S.null conflictOut ->
           error $ "Compiler error: conflicting outputs in " ++ show (e1,e2)
         | let -> Effect (M.union (effInputs e1) (effInputs e2)) $
                  S.union (effOutputs e1) (effOutputs e2)
allOf :: [Effect] -> Effect
allOf = foldr (&) nothing
nothing = Effect M.empty S.empty
--Depends on but does not consume, e.g. mload depends on Memory.
reads :: State -> Effect
reads s = Effect (M.singleton s Borrows) S.empty
modifies :: State -> Effect
modifies s = Effect (M.singleton s Consumes) (S.singleton s)
consumes :: State -> Effect
consumes s = Effect (M.singleton s Consumes) S.empty
consumesAll :: [State] -> Effect
consumesAll = allOf . map consumes
--Used by jump:
--TODO keep updated when I add new resources!
consumesAllState = consumesAll allState
allState = [Memory,
            Storage,
            TStorage,
            Calldata,
            Returndata,
            ExtState,
            Other
           ]
--The state values that can be borrowed, returned or consumed.
--Will be more general than Ptr regions in future, e.g. gas() should modify
--Gas, CALL should modify selfbalance etc. Those can be overapproximated for
--now by using Other.
--Tricky FW: more detailed resources, such as memory slices referring to
--symbolic addresses in Core. I'll need to param State to avoid making
--Opcodeinfo (which also serves other stages) dependent on Core.
--That's a prerequisite for ops which consume but do not produce a resource,
--e.g. free(ptr), call consuming current returndata or alloc consuming a
--splittable allocPtr resource to ensure uniqueness but commutativity.
--There are also no non-branching ops which produce s but do not consume it,
--FW ex: alloc producing a fresh pointer memory slice.
data State = Memory
           | Storage
           | TStorage
           | Calldata
           | Returndata
           | ExtState --external contracts, storage etc
           | Other --everything else
  deriving (Eq,Ord,Read,Show)

--Convention: maps from lowercase strings
opcodes :: Map String OpcodeInfo
opcodes = M.fromList $ 
  [returning "stop" 0 0 0 False] ++
  [op2 nm opcode gas
  | (opcode,(nm,gas)) <- zip [1..] $ table
                         ["add 3",
                          "mul 5",
                          "sub 3",
                          "div 5",
                          "sdiv 5",
                          "mod 5",
                          "smod 5"
                         ]
  ] ++
  [pureOp nm opcode 3 True gas
  | (nm,opcode,gas) <- [("addmod",8,8),
                        ("mulmod",9,8)]] ++
  --Has a variable gas cost
  [op2 "exp" 0x0a 10,
   op2 "signextend" 0x0b 5] ++
  threeOps 0x10 "lt gt slt sgt eq" ++
  oneOp "iszero" 0x15 ++
  threeOps 0x16 "and or xor" ++
  oneOp "not" 0x19 ++
  threeOps 0x1a "byte shl shr sar" ++
  --keccak256 is the name in https://ethereum.org/developers/docs/evm/opcodes/
  --TODO add sha3 synonym to EVM.evmc
  --Note: the user will almost certainly hash at least one byte, so the
  --min cost in practice is 36.
  [impureOp (reads Memory) "keccak256" 0x20 2 True 30] ++
  [env "address" 0x30] ++
  --Choice: selfbalance falls under other for now
  --Note the min cost is highly misleading; repeated loads of the same hot
  --balance is unlikely.
  [impureOp (reads Other & reads ExtState) "balance" 0x31 0 True 100] ++
  [env nm opcode
  | (opcode,nm) <- zip [0x32..] $ words "origin caller callvalue"] ++
  [impureOp (reads Calldata) "calldataload" 0x35 1 True 3] ++
  --TODO put size into another State? It determines content...
  [impureOp (reads Calldata) "calldatasize" 0x36 0 True 2] ++
  [impureOp (reads Calldata & modifies Memory) "calldatacopy" 0x37 3 False 3] ++
  --It's just a constant... in any given compiled program.
  [pureOp "codesize" 0x38 0 True 2] ++
  --Similarly, should code be assumed to be fixed in codecopy?
  [impureOp (modifies Memory) "codecopy" 0x39 3 True 3] ++
  [env "gasprice" 0x3a] ++
  --Again, highly misleading min gas costs for all ops that touch ExtState.
  [impureOp (reads ExtState) "extcodesize" 0x3b 1 True 100] ++
  [impureOp (reads ExtState & modifies Memory)
    "extcodecopy" 0x3c 4 False 100] ++
  [impureOp (reads Returndata) "returndatasize" 0x3d 0 True 2] ++
  [impureOp (reads Returndata & modifies Memory)
   "returndatacopy" 0x3e 3 False 3] ++
  [impureOp (reads ExtState) "extcodehash" 0x3f 1 True 100] ++
  [impureOp (reads Other) "blockhash" 0x40 1 True 20] ++
  [env nm opcode | (opcode,nm) <- zip [0x41..] $
    words "coinbase timestamp number prevrandao gaslimit chainid"] ++
  [let (a,b) = (env "selfbalance" 0x47)
   in (a,b{oiMinGas = 5})] ++
  [env "basefee" 0x48] ++
  [let (a,b) = (env "blobhash" 0x49)
   in (a,b{oiMinGas = 3})] ++
  [env "blobbasefee" 0x4a] ++
  [("pop",OI{oiOpcode = 0x50,
             oiMinGas = 2,
             oiArgArity = 0,
             oiBehavior = Pop
            })] ++
  [impureOp (reads Memory) "mload" 0x51 1 True 3] ++
  [impureOp (modifies Memory) "mstore" 0x52 2 False 3] ++
  [impureOp (modifies Memory) "mstore8" 0x53 2 False 3] ++
  [impureOp (reads Storage) "sload" 0x54 1 True 100] ++
  [impureOp (modifies Storage) "sstore" 0x55 2 False 100] ++
  [("jump", jumpy 0x56 1 8), ("jumpi", jumpy 0x57 2 10)] ++
  --PC isn't helpful in Core, since basic blocks and the ops they're
  --composed of may be arranged in arbitrary order.
  --Each PC instruction will return a constant, but each may be different...
  --FW TODO: add longjmp, setjmp? Problem: stack leak.
  [env "pc" 0x58] ++
  [impureOp (reads Memory) "msize" 0x59 0 True 2] ++
  --TODO add a separate Gas state
  [impureOp (modifies Other) "gas" 0x5a 0 True 2] ++
  --JUMPDEST is () -> (), pointless in C/Core.
  [pureOp "jumpdest" 0x5b 0 False 1] ++
  [impureOp (reads TStorage) "tload" 0x5c 1 True 100] ++
  [impureOp (modifies TStorage) "tstore" 0x5d 2 False 100] ++
  [impureOp (modifies Memory) "mcopy" 0x5e 3 False 3] ++
  [pureOp "push0" 0x5f 0 True 2] ++
  [("push" ++ show n,
    OI {oiOpcode = op,
        oiMinGas = 2,
        oiArgArity = 0,
        oiBehavior = Push n
       })
  | (op,n) <- zip [0x60..] [1..32]] ++
  --Code smell: copy-pasting... but this file will rarely need to be updated.
  --dupN could be said to have an arity of 1, and swapN n+1...
  [("dup" ++ show n,
    OI {oiOpcode = op,
        oiMinGas = 3,
        oiArgArity = 0,
        oiBehavior = Dup n
       })
  | (op,n) <- zip [0x80..] [1..16]] ++
  [("swap" ++ show n,
    OI {oiOpcode = op,
        oiMinGas = 3,
        oiArgArity = 0,
        oiBehavior = Swap n
       })
  | (op,n) <- zip [0x90..] [1..16]] ++
  [impureOp (modifies Other) ("log"++show n) op (2+n) False (375*(n+1))
  | (op,n) <- zip [0xa0..] [0..4]] ++
  --What does CREATE do? It may modify the balance and nonce (Other),
  --extstate (directly), storage and tstorage (via calls).
  --It does not modify calldata, memory, or returndata (?).
  --However, it does depend on memory.
  --Its massive min cost should naively encourage checks for revert
  --conditions before the create. However, by marking pessimistic paths
  --with intensity ~0 you should get code optimized for the optimistic path.
  [impureOp (reads Memory &
             allOf (map modifies [Storage, TStorage, ExtState, Other]))
    "create" 0xf0 3 True 32000] ++
  --What does call modify? Everything but calldata.
  --FW TODO: just as function types could be tagged with the state they may
  --read and consume, contract addresses could as well.
  [impureOp (allOf (map modifies [Memory,Storage,TStorage,
                                  Returndata,ExtState,Other]))
    "call" 0xf1 7 True 100] ++
  [impureOp (allOf (map modifies [Memory,Storage,TStorage,
                                  Returndata,ExtState,Other]))
    "callcode" 0xf2 7 True 100] ++
  --return consumes all state but returndata and calldata
  [("return", (jumpy 0xf3 2 0){oiBehavior = Branching $
                              consumesAll [Memory,Storage,TStorage,
                                        ExtState,Other]
                            })] ++
  [impureOp (allOf (map modifies [Memory,Storage,TStorage,
                                  Returndata,ExtState,Other]))
    "delegatecall" 0xf4 6 True 100]  ++
  [impureOp (reads Memory &
             allOf (map modifies [Storage, TStorage, ExtState, Other]))
    "create2" 0xf5 4 True 32000] ++
  --staticcall modifies gas... but so does almost every other op
  --FW TODO in Core: recognize when memory isn't modified
  [impureOp (allOf (map modifies [Memory,Returndata]))
            "staticcall" 0xfa 6 True 100] ++
  --revert and invalid discard changes to state, except gas... but since
  --the caller should assume Other/Gas may have been updated, there's no
  --need to pass it yet.
  [("revert",(jumpy 0xfd 2 0){oiBehavior = Branching $ consumes Memory})] ++
  --The only reason to emit invalid is to save 400 gas by avoiding using
  --PUSH0 PUSH0 REVERT in a malicious revert path where you don't mind
  --burning the caller's gas.
  --The minimum gas cost is technically 0...
  [("invalid", (jumpy 0xfe 0 0){oiBehavior = Branching nothing})] ++
  --selfdestruct deletes the contract's own code if it was created.
  --Note it's deprecated and unsupported by Core.
  [("selfdestruct", (jumpy 0xff 1 5000){oiBehavior =
                                        Branching $ consumesAll [
                                           Storage,TStorage,ExtState,Other
                                           ]})]
    
--Jumps consume all state
jumpy opcode arity cost = OI {
  oiOpcode = opcode,
  oiMinGas = cost,
  oiArgArity = arity,
  oiBehavior = Branching consumesAllState
  }
  
--A sequence of op2s with gas cost 3
threeOps opcode str =
  [op2 nm opcode 3 | (opcode,nm) <- zip [opcode..] $
    words str
                   ]
--not, iszero
oneOp nm opcode = [pureOp nm opcode 1 True 3]
--Instrs like TIMESTAMP, but not GAS (which modifies Other because gas calls
--are not commutative)
env nm opcode = impureOp (reads Other) nm opcode 0 True 2
  
op2 nm opcode gas = pureOp nm opcode 2 True gas
pureOp = impureOp nothing
impureOp eff nm opcode arity returns gas =
  (nm, OI {
      oiOpcode = opcode,
      oiMinGas = gas,
      oiArgArity = arity,
      oiBehavior = Normal {obReturns = returns,
                           obEffect = eff
                          }
      })
returning nm opcode arity gas readsMem =
  (nm, OI {
      oiOpcode = opcode,
      oiMinGas = gas,
      oiArgArity = arity,
      oiBehavior = Branching $ consumesAll $
        [Memory | readsMem] ++
        [Storage,TStorage,ExtState,Other]
      })                                   

--Sugar for opcode-gas info
table :: [String] -> [(String,Int)]
table = map (\str ->
               let [nm,show_n] = words str
               in (nm, read show_n))
