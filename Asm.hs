{-# Language LambdaCase, DeriveDataTypeable #-}
module Asm where

import Data.Data
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)
import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
--import Data.ByteString (ByteString(..))
--import qualified Data.ByteString as B
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans.Except

--A datatype for generating asm for the codegen; todo a monad for codegen
--Goal: keep the DT minimal while supporting linking
--When linking, give each blob new anon labels.
data Asm = Push Int Integer
         | PushLabel Int Label
         | Dup Int
         | Swap Int
         | Opcode String
         | PlaceLabel Label
         --Why allow BasePlus? To allow pointers into following arrays or
         --structs, for example.
         | DefLabel Label LabelValue
         --No need for .data; data is included directly in the asm
         | Bytes [Int]
         | UseLabel Int Label
         --PushRelative Label Int would let you make code relocatable.
         --push base + k would become PC + k', where k' = k - the byte offset
         --of the PushRelative in the object file
  deriving (Eq,Ord,Read,Show,Data)
data Label = LNamed String | LAnon Int
  deriving (Eq,Ord,Read,Show,Data)
--data Datum = Bytes [Int] | UseLabel Int Label
--  deriving (Eq,Ord,Read,Show,Data)
--Each base+k label value has byte size 2
data LabelValue = Exactly Int [Int] | BasePlus Int
  deriving (Eq,Ord,Read,Show,Data)
--Getting rid of anon labels in the ObjectFile...
data SymbolicValue 
--Problem: this format doesn't allow including a slize of a label's value in
--code, e.g. the bottom 2 bytes of a uint32. Does that matter in practice?
data ObjectFile = OF {
  --Both defined and placed
  exportedLabels :: Map String LabelValue,
  --Anon labels start at 1; each anon label used must also be set.
  anonLabels :: Map Int LabelValue,
  --In case you allocate and then don't use an anon label
  anonLabelCtr :: Int,
  --The Int is expected label size
  --Extern labels aren't explicitly declared; they and their expected size
  --are inferred during assembly.
  importedLabels :: Map String Int,
  --When the Exact value of a label is set internally, you can set the use
  --sites to constant bytes immediately and don't need to declare a use site
  --and substitute later.
  --Labels and templates alternate; merge adjacent bytestring sections via
  --concatenation.
  --Why use [Int] rather than ByteString? Simplicity, since performance isn't
  --really needed for 24kB smart contracts.
  template :: [Either Label [Int]],
  --The size of the code in bytes
  byteSize :: Int
  }
  deriving (Eq,Ord,Read,Show,Data)

incLabels base = everywhere $ mkT (\case
                                      LAnon n -> LAnon $ base + n
                                      l -> l)
incBase offset = everywhere $ mkT (\case
                                      BasePlus k -> BasePlus (offset+k)
                                      l -> l)
{-
data Asm = Push Int Integer
         | PushLabel Int Label
         | Dup Int
         | Swap Int
         | Opcode String
         | PlaceLabel Label
         | DefLabel Label Int [Int]
         --No need for .data; data is included directly in the asm
         | Bytes [Int]
         | UseLabel Int Label
-}
asmSize :: Asm -> Int
asmSize = \case
  Push n _ -> n + 1
  PushLabel n _ -> n
  Dup _ -> 1
  Swap _ -> 1
  Opcode _ -> 1
  Bytes bs -> length bs
  UseLabel n _ -> n
  decl -> 0

--Errors:
--multiple definitions of labels
--conflicting uses of any label, imported or defined
--label uses which conflict with definition
--anon label used but not defined
--nonexistent opcodes
--push, dup or swap out of range (1..16)
data AsmError = DuplicateLabelDefs Label LabelValue LabelValue
              | ConflictingLabelUses Int Int
              | LabelUseConflictsWithDef Int Int
              | UndefinedAnonLabel Int
              | NonexistentOpcode String
              | InstructionOutOfRange String Int
  deriving (Eq,Ord,Read,Show)
--First pass: get defined and used labels, max anon label count, compute
--template.
data AS = AS {asExportedLabels :: Map String LabelValue,
              asAnonLabels :: Map Int LabelValue,
              asUsedLabels :: Map Label Int,
              asOffset :: Int
             }
type Template = [Either Label [Int]]
type Assembler = ExceptT AsmError (WriterT Template (State AS))
runAssembler :: Assembler a -> AS -> (Either AsmError a, Template, AS)
runAssembler m as =
  let ((a,b),c) = flip runState as $ runWriterT $ runExceptT m
  in (a,b,c)
puke :: AsmError -> Assembler a
puke = throwE
emit :: Int -> (Either Label [Int]) -> Assembler ()
emit n x = do
  tell [x]
  s <- get
  put $ s{asOffset = asOffset s + n}
emitBytes bs = emit (length bs) (Right bs)
--Also reports the label was used
emitLabel :: Int -> Label -> Assembler ()
emitLabel len l = do
  as <- get
  case M.lookup l $ asUsedLabels as of
    Just len'
      | len' /= len -> puke $ ConflictingLabelUses len' len
      | let -> return ()
    Nothing -> put $ as{asUsedLabels = M.insert l len $ asUsedLabels as}
  emit len (Left l)
--TODO use lenses...
setLabel l lv =
  case l of
    LNamed str -> help asExportedLabels (\as m -> as{asExportedLabels = m})
      LNamed str
    LAnon n -> help asAnonLabels (\as m -> as{asAnonLabels = m})
      LAnon n
  where help getter putter con x = do
          as <- get
          let exps = getter as
          case M.lookup x exps of
            Just lv'
              | lv' /= lv -> puke $ DuplicateLabelDefs (con x) lv' lv
              | let -> return ()
            Nothing -> put $ putter as $ M.insert x lv exps

handleAsm :: Asm -> Assembler ()
handleAsm = \case
  Push len n ->
    checkRange "push" 0 32 len $
    emitBytes $ push2Bytes len n
  PushLabel len l ->
    checkRange "push" 0 32 len $ do
        emitBytes [0x5f + len]
        emitLabel len l
  Dup n ->
    checkRange "dup" 1 16 n $ emitBytes [0x80 + n]
  Swap n ->
    checkRange "swap" 1 16 n $ emitBytes [0x90 + n]
  Opcode str -> error "TODO port opcodes from MC4"
  PlaceLabel l -> do
    off <- asOffset <$> get
    setLabel l (BasePlus off)
  DefLabel l lv -> setLabel l lv
  Bytes bs -> emitBytes bs
  UseLabel len l -> emitLabel len l
checkRange instr lo hi n act
  | n < lo || n > hi = puke $ InstructionOutOfRange instr n
  | let = act
  
--Note: the bounds check on len is done in handleAsm, not here
push2Bytes :: Int -> Integer -> [Int]
push2Bytes len n = (0x5f + len) : integer2Bytes len n
integer2Bytes len n
  | n < 0 = integer2Bytes len (n + 2 ^ 256)
  | let n' = n `mod` (256 ^ len) = reverse $ i2b len n' 
i2b 0 _ = []
i2b len n = fromInteger (n `mod` 256) :
            i2b (len-1) (n `div` 256)
{-
exportedLabels :: Map String LabelValue,
anonLabels :: Map Int LabelValue,
importedLabels :: Map String Int,
-}

{-
data Asm = Push Int Integer
         | PushLabel Int Label
         | Dup Int
         | Swap Int
         | Opcode String
         | PlaceLabel Label
         --Why allow BasePlus? To allow pointers into following arrays or
         --structs, for example.
         | DefLabel Label LabelValue
         --No need for .data; data is included directly in the asm
         | Bytes [Int]
         | UseLabel Int Label
-}

--Add anonLabelCtr parameter; it's to be provided by the code generator monad.
--Other info such as stack offset doesn't need to be passed on.
assemble :: [Asm] -> Either AsmError ObjectFile
assemble asms =
  case runAssembler asms $ AS M.empty M.empty M.empty 0 of
    (Left err,_,_) -> Left err
    (Right (),template,as) -> undefined
    --Check all used anon labels are defined
    --Check the offset < 24k
    --Remove all defined labels from asUsedLabels; the rest are imports
    --Substitute all label uses of exactly defined labels for bytes
    --Remove the anon ones from anonLabels

--Improvement: no reference to an anon label should remain in the object
--file, only their count.

--When setting labels in an OF, remove them from imports if they're global

--This concatenates contiguous byte sections.
--Note: it doesn't check the bytes you substitute labels for are of the
--correct length; checks in assemble/merge should do that.
setLabelsTemplate :: Map Label [Int] -> Template -> Template
setLabelsTemplate l2bs = concatContiguousBytes .
                         map (\case
                                 Left l ->
                                   case M.lookup l l2bs of
                                     Just bs -> Right bs
                                     Nothing -> Left l
                                 Right bs -> Right bs)
  where concatContiguousBytes = \case
          [] -> []
          eb : ebls ->
            case eb of
              Right bs -> ccbs [bs] ebls
              Left l -> Left l : concatContiguousBytes ebls
        ccbs bss = \case
          [] -> concat $ reverse bss
          Right bs : ebls -> 
--Merging object files:
--set base and anon offset for each object
--concatenate templates, merge exports; eliminate imports defined by any
--module.

--Converting an object file to an executable:
--set base to 0, converting BasePlus k to exactly k
--convert label uses to bytes; warn of undefined labels but fill in zeroes by
--default.
