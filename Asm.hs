{-# Language LambdaCase, DeriveDataTypeable #-}
module Asm where

import Opcodes (mnemonics)

import Data.Data
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)
import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
--import Data.ByteString (ByteString(..))
--import qualified Data.ByteString as B
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans.Except
import Control.Monad (filterM)

--A datatype for generating asm for the codegen; todo a monad for codegen
--Goal: keep the DT minimal while supporting linking
--When linking, give each blob new anon labels.
--EVMC's Codegen module doesn't use Push, Dup or Swap; those can be
--implemented with Opcode, Bytes and UseLabel.
data Asm = --Push Int Integer
           PushLabel Int Label
         -- | Dup Int
         -- | Swap Int
         | Opcode String
         | PlaceLabel Label
         --Why allow BasePlus? To allow pointers into following arrays or
         --structs, for example.
         | DefLabel Label LabelValue
         --No need for .data; data is included directly in the asm
         | Bytes [Int]
         --UseLabel now takes an additional offset arg before len, indicating
         --the offset into the label value to slice. Ex: lab = 0xaabb =>
         --UseLabel 1 1 becomes 0xbb.
         | UseLabel Int Int Label
         --PushRelative Label Int would let you make code relocatable.
         --push base + k would become PC + k', where k' = k - the byte offset
         --of the PushRelative in the object file

         --Comments for debugging
         | Comment String
  deriving (Eq,Ord,Read,Show,Data)
data Label = LNamed String | LAnon Int
  deriving (Eq,Ord,Read,Show,Data)
--data Datum = Bytes [Int] | UseLabel Int Label
--  deriving (Eq,Ord,Read,Show,Data)
--Each base+k label value has byte size 2
data LabelValue = Exactly Int [Int] | BasePlus Int
  deriving (Eq,Ord,Read,Show,Data)
labelValueLen :: LabelValue -> Int
labelValueLen = \case
  Exactly len _ -> len
  BasePlus _ -> 2
--Getting rid of anon labels in the ObjectFile...
data TemplateValue = ExactlyBytes [Int]
                   --CodeBasePlus off len k: (codebase+k).slice(off,len)
                   | CodeBasePlus Int Int Int
                   | ReadLabel Int Int Label
  deriving (Eq,Ord,Read,Show,Data)
type Template = [TemplateValue]
--Problem: this format doesn't allow including a slize of a label's value in
--code, e.g. the bottom 2 bytes of a uint32. Does that matter in practice?
data ObjectFile = OF {
  --Both defined and placed
  exportedLabels :: Map String LabelValue,
  --Anon labels start at 1; each anon label used must also be set.
  --anonLabels :: Map Int LabelValue,
  --In case you allocate and then don't use an anon label
  --anonLabelCtr :: Int,
  --Removed because other modules don't need to care about local labels
  
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
  template :: Template,
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
  --Push n _ -> n + 1
  PushLabel n _ -> n
  --Dup _ -> 1
  --Swap _ -> 1
  Opcode _ -> 1
  Bytes bs -> length bs
  UseLabel _off n _ -> n
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
              | LabelUseConflictsWithDef Label Int Int
              | UndefinedAnonLabel Int
              | NonexistentOpcode String
              | InstructionOutOfRange String Int
              | CodeSizeLimitExceeded Int
  deriving (Eq,Ord,Read,Show)
--First pass: get defined and used labels, max anon label count, compute
--template.
data AS = AS {asExportedLabels :: Map String LabelValue,
              asAnonLabels :: Map Int LabelValue,
              asUsedLabels :: Map Label Int,
              asCodeOffset :: Int
             }

type Assembler = ExceptT AsmError (WriterT Template (State AS))
runAssembler :: Assembler a -> AS -> (Either AsmError a, Template, AS)
runAssembler m as =
  let ((a,b),c) = flip runState as $ runWriterT $ runExceptT m
  in (a,b,c)
puke :: AsmError -> Assembler a
puke = throwE
emit :: Int -> TemplateValue -> Assembler ()
emit n x = do
  tell [x]
  s <- get
  put $ s{asCodeOffset = asCodeOffset s + n}
emitBytes bs = emit (length bs) (ExactlyBytes bs)
--Also reports the label was used
--Change: now takes an offset for slicing the label.
--The length of the label slice may now differ from the length of the value
--bound to the label; that should not raise ConflictingLabelUses.
--ReadLabel must also be modified to take the slice params off and len.
emitLabel :: Int -> Int -> Label -> Assembler ()
emitLabel off len l = do
  as <- get
  case M.lookup l $ asUsedLabels as of
    Just len'
      -- | len' /= len -> puke $ ConflictingLabelUses len' len
      | let -> return ()
    Nothing -> put $ as{asUsedLabels = M.insert l len $ asUsedLabels as}
  emit len $ ReadLabel off len l
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
handleAsm = \case {-
  Push len n ->
    checkRange "push" 0 32 len $
    emitBytes $ push2Bytes len n -}
  PushLabel len l ->
    checkRange "push" 0 32 len $ do
        emitBytes [0x5f + len]
        emitLabel 0 len l {-
  Dup n ->
    checkRange "dup" 1 16 n $ emitBytes [0x7f + n]
  Swap n ->
    checkRange "swap" 1 16 n $ emitBytes [0x8f + n]
   -}
  Opcode str ->
    case M.lookup str mnemonics of
      Just op -> emitBytes [op]
      Nothing -> puke $ NonexistentOpcode str
  PlaceLabel l -> do
    off <- asCodeOffset <$> get
    setLabel l (BasePlus off)
  DefLabel l lv -> setLabel l lv
  Bytes bs -> emitBytes bs
  UseLabel off len l -> emitLabel off len l
  Comment _ -> return ()
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

assemble :: [Asm] -> Either AsmError ObjectFile
assemble asms =
  case runAssembler (mapM_ handleAsm asms) $ AS M.empty M.empty M.empty 0 of
    (Left err,_,_) -> Left err
    (Right (),tem,as) -> do
       --Check the offset <= 24k
      let sz = asCodeOffset as
      if sz > 24000
        then Left $ CodeSizeLimitExceeded sz
        else Right ()
      --Check all used anon labels are defined
      let usedAnon = M.toList (asUsedLabels as) >>=
            (\case (LAnon n,len) -> [(n,len)]
                   _ -> [])
      mapM_ (\(n, len) ->
               case M.lookup n (asAnonLabels as) of
                 Just lv
                   | labelValueLen lv /= len ->
                     Left $ LabelUseConflictsWithDef (LAnon n) len
                     (labelValueLen lv)
                   | let -> Right ()
                 Nothing -> Left $ UndefinedAnonLabel n) usedAnon
      --Remove all defined labels from asUsedLabels; the rest are imports
      let usedNamed = M.toList (asUsedLabels as) >>=
            (\case (LNamed nm,len) -> [(nm,len)]
                   _ -> [])
      imps <- M.fromList <$> filterM (\(nm,len) ->
                          case M.lookup nm $ asExportedLabels as of
                            Just lv
                              | labelValueLen lv /= len ->
                                Left $ LabelUseConflictsWithDef (LNamed nm) len
                                (labelValueLen lv)
                              | let -> return False
                            Nothing -> return True) usedNamed
      --Substitute defined labels for either bytes or CodeBasePlus in
      --template.
      let exps = asExportedLabels as
      let template' = setLabelsTemplate
            (M.union (M.mapKeys LNamed exps)
            (M.mapKeys LAnon $ asAnonLabels as)) tem
      return $ OF {
        exportedLabels = exps,
        importedLabels = imps,
        template = template',
        byteSize = asCodeOffset as
        }
--Improvement: no reference to an anon label should remain in the object
--file, only their count.

--When setting labels in an OF, remove them from imports if they're global

--This concatenates contiguous byte sections.
--Note: it doesn't check the bytes you substitute labels for are of the
--correct length; checks in assemble/merge should do that.
--If I passed a Map Label TemplateValue I could set a label to another label...
--Problem: now that labels can be sliced, it must be possible to slice
--BasePlus as well.
setLabelsTemplate :: Map Label LabelValue -> Template -> Template
setLabelsTemplate m = concatBytes .
  map (\case ReadLabel off len l ->
               case M.lookup l m of
                 Just (Exactly _ bs) -> ExactlyBytes $ take len $ drop off $
                                        bs ++ repeat 0
                 Just (BasePlus k) -> CodeBasePlus off len k
                 Nothing -> ReadLabel off len l
             tv -> tv)
concatBytes :: Template -> Template
concatBytes = let
  cb bss = \case
    ExactlyBytes bs:tvs -> cb (bs:bss) tvs
    tvs -> ExactlyBytes (concat $ reverse bss) : concatBytes tvs
  in \case
  [] -> []
  ExactlyBytes bs:tvs -> cb [bs] tvs
  tv:tvs -> tv : concatBytes tvs

--Used to fill in imports
--If m[nm] conflicts with an export, error
--If nm's length conflicts with the import, error
--If nm is not imported, ignore it
--Update the template
--Question: should this throw an AsmError?
--This should take a Map String LabelValue so you can merge objs!
--Change: setLabels now supports ReadLabel's that slice the given label.
--If len is greater than the length of the label value, zero bytes are appended.
setLabels :: Map String [Int] -> ObjectFile -> Either String ObjectFile
setLabels m obj = do
  let coll = S.intersection (M.keysSet m) (M.keysSet $ exportedLabels obj)
  if coll /= S.empty
    then Left $ "Labels to set collide with exports in " ++ show coll
    else return ()
  mapM_ (\(nm,bs) ->
          case M.lookup nm $ importedLabels obj of
            Just len
              | len /= length bs ->
                Left $ "Bytestring for name doesn't match imported length: "
                ++ show (nm,bs,len)
            _ -> return ()
       )
    $ M.toList m
  let imps' = M.withoutKeys (importedLabels obj) (M.keysSet m)
      temp' = concatBytes $ map (\case
                                    ReadLabel off len (LNamed nm)
                                      | Just bs <- M.lookup nm m ->
                                        ExactlyBytes $ take len $ drop off $
                                        bs ++ repeat 0
                                    tv -> tv) $ template obj
  return $ obj{importedLabels = imps',
               template = temp'
              }
--Merging object files:
--set base and anon offset for each object
--concatenate templates, merge exports; eliminate imports defined by any
--module.
--Does not set the code base!
--Note it just concatenates the code; templates with holes in them aren't
--supported.
--Do I need this? The C/IR level will have all the necessary info about
--labels...
mergeObjectFiles :: [ObjectFile] -> Either String ObjectFile
mergeObjectFiles = error "TODO" --foldlM mergeOFs nullOF
nullOF = OF M.empty M.empty [] 0
--If there are clashing exports, error
--If there's a length mismatch between export and import, error
--Remove labels exported by either from imports
mergeOFs :: ObjectFile -> ObjectFile -> Either String ObjectFile
mergeOFs o1 o2 = undefined

--Converting an object file to an executable:
--set base to 0, converting BasePlus k to exactly k
--convert label uses to bytes; warn of undefined labels but fill in zeroes by
--default.
toExe :: ObjectFile -> (Set String,[Int])
toExe obj =
  let defaults = M.map (flip replicate 0) $ importedLabels obj
      Right obj' = setLabels defaults obj
  in (M.keysSet $ importedLabels obj,
      case template $ setCodeBase 0 obj' of
        [ExactlyBytes bs] -> bs)
setCodeBase :: Int -> ObjectFile -> ObjectFile
setCodeBase off obj = obj{
  exportedLabels = M.map (\case
                             BasePlus k -> Exactly 2 $
                                           integer2Bytes 2 $ fromIntegral $
                                           off + k
                             x -> x
                         ) $
                   exportedLabels obj,
  template = concatBytes $ map (\case CodeBasePlus o len k ->
                                        ExactlyBytes $
                                        take len $ drop o $
                                        (integer2Bytes 2 $
                                         fromIntegral $ off+k) ++ repeat 0
                                      x -> x
                               )
             $ template obj
  }
