module Opcodes where

import Data.Map(Map(..))
import qualified Data.Map as M
--TODO replace with opcodes module from MC4

mnemonics :: Map String Int
mnemonics = M.fromList $
  instrs 0x00 "stop add mul sub div sdiv mod smod addmod mulmod exp signextend"
  ++
  instrs 0x10 "lt gt slt sgt eq iszero and or xor not byte shl shr sar"
  ++
  instrs 0x20 "keccak256" --AKA sha3
  ++ [("sha3",0x20)]
  ++
  instrs 0x30 ("address balance origin caller callvalue calldataload " ++
               "calldatasize calldatacopy codesize codecopy gasprice " ++
               "extcodesize extcodecopy returndatasize returndatacopy " ++
               "extcodehash blockhash coinbase timestamp number prevrandao " ++
               "gaslimit chainid selfbalance basefee blobhash blobbasefee")
  ++
  instrs 0x50 ("pop mload mstore mstore8 sload sstore jump jumpi pc msize " ++
               "gas jumpdest tload tstore mcopy") ++
  variants 0x5f "push" 0 32 ++
  variants 0x80 "dup" 1 16 ++
  variants 0x90 "swap" 1 16 ++
  variants 0xa0 "log" 0 4 ++
  instrs 0xf0 "create call callcode return delegatecall create2" ++
  [("staticcall",0xfa)] ++
  instrs 0xfd "revert invalid selfdestruct"
instrs :: Int -> String -> [(String,Int)]
instrs off ws = zip (words ws) [off..]
variants opcode name lo hi = zip [name ++ show n | n <- [lo..hi]] [opcode..]
