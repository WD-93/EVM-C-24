{-# LANGUAGE LambdaCase, GADTs #-}
module IR1 where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Fail

import DTs
--The first stage of compilation from AST: word-level ops with structured
--patterns.
--Function call is treated as an op.
data IRT = Mem --has no runtime repr
         | Word Int T --nth word of C-level t; 1-indexed
  deriving (Eq,Ord,Read,Show)
--Name mangling: nth word of local x becomes x#n
data IR = [(Name,IRT)] := (Operator,[Name])
         | Ifte Name [IR] [IR]
         | While [IR] Name [IR]
         | DoWhile [IR] [IR] Name --body, cond
         | Return [Name]
         | TailCall Name [Name]
  deriving (Eq,Ord,Read,Show)
data Operator = Push StaticValue
              | Opcode String
              | Call --args: f, args, ret
              | Reduce Name --a commutative and associative opcode,
                --used for truthy
              | Copy --x = y => x = copy [y] 
  deriving (Eq,Ord,Read,Show)
--Ret and f are created by push staticValue
data StaticValue = Const Integer
                 | LabelConst Name
  deriving (Eq,Ord,Read,Show)

--Convert a defun to a sequence of IR1 ops.
--If any modification to $mem is made, it must be returned.
--If it happens in an ifte branch that returns, don't propagate (the branch
--doesn't have a successor).
--Reader: module (only function types relevant for now).
--State: C variable scope
--Only PVar and PTup assignment supported for now
--x = y becomes a renaming, but it's a pseudo-op.
--Emit: IR1 ops
type Seq = ExceptT SeqError
  (ReaderT SeqR
   (WriterT [IR]
    (State SeqS)))
runSeq :: Seq a -> SeqR -> SeqS -> (Either SeqError a,
                                     [IR],
                                     SeqS)
runSeq seq seqr s = let
  x1 = runExceptT seq
  x2 = runReaderT x1 seqr
  x3 = runWriterT x2
  x4 = runState x3 s
  in case x4 of
       ((ei,ir),s) -> (ei,ir,s)
data SeqError = UnboundVar Name
              --The stuff that can go wrong in an op
              | IlltypedLHS Name IRT IRT
              | DuplicateVarsInLHS Name (Set Name)
              | Can'tCopyUnboundIRVar Name
              | UnboundVarInOpRHS Name [(Name,IRT)] Operator [Name]

              | Couldn'tLookupVarTypeInEDSL Name
              | BadArgsInEDSL Operator [EVar]
              | BadFirstRHSInAssign Name (Maybe IRT) [Name]
              | BadFunctionType Name T
              | Can'tAssignToFunction Name E
  deriving (Eq,Ord,Read,Show)
--pronounced seek s...
data SeqS = SS {
  --IR vars = v#1..n for each v in C locals, plus anonymous vars and $mem
  irLocalTypes :: Map Name IRT,
  cLocalTypes :: Map Name T,
  anonVarCounter :: Int --makes $anonN
  }
  deriving (Eq,Ord,Read,Show)
--So I can add info about the function being compiled, specifically the return
--type but maybe more stuff in future (opt choices?).
data SeqR = SR {
  seqrModule :: Module,
  seqrFunction :: D
               }
  deriving (Eq,Ord,Read,Show)
askModule :: Seq Module
askModule = seqrModule <$> ask
askReturnType :: Seq T
askReturnType = do
  Defun nm t _lhs _body <- seqrFunction <$> ask
  case t of
    a :-> b -> return b
    _ -> throwE $ BadFunctionType nm t
{-
Consider
while(e)
 tmp = x
 x = y
 y = tmp

The renaming ops become noops in the next stage, but they change the stack
layout. Let's say the starting layout in loop is x,y,vs. The target layout
at the end of the loop becomes y,x,vs after translation; consequently, a swap
must be emitted.
Invariant: only one version of a C-level var word is live at a time; garbage
words may be substituted for any other garbage. Avoid leaving any garbage at
the end of a SLC?
-}
seqDefun :: D -> Seq ()
seqDefun = undefined

--The scope is reset at the end
--
seqBlock :: Block -> Seq ()
seqBlock = undefined
--For now, support only assignment to x. Later: tuple
--For now, no tail call support
seqS :: S -> Seq ()
seqS = \case
  --TODO do name info lookup, give informative errors on assignment to
  --functions and other immutables.
  PVar x DTs.:= e -> do
    ni <- getCNameInfo x
    case ni of
      IsFunction _ -> throwE $ Can'tAssignToFunction x e
      --The variable is already in scope
      --Need to do variable coercion so x : Word = 3 works
      IsLocal t -> do
        (t',ws) <- seqE e
        cws <- softCoerce t t' ws
        assign x cws
      --The variable is free, so we'll accept any type and add the var to the
      --C scope.
      IsUnbound -> do
        (t,ws) <- seqE e
        assign x ws --TODO add to C scope
  --The last argument of any function is $ret : tword
  --The first value to return (and the first result of any call) is $mem
  --The second is $ret!
  --State variables in return should not affect the stack target.
  --TODO add tail call support for return f(args), where f is not a primfun.
  --Note: expressions may modify $mem, but seqE should never return it.
  DTs.Return e -> do
    t <- askReturnType
    (t',ws) <- seqE e
    cws <- softCoerce t t' ws
    emit $ IR1.Return $ ["$mem","$ret"] ++ cws
  --Applies truthy to e, returning one word
  DTs.Ifte e bthen belse -> undefined
  DTs.While e block -> undefined
--You need to know the *word* vars returned to use them;
--if $mem is involved it remains the same.
--Also returns the type (which only depends on global info, locals and
--subexprs); type checking is fused into IR codegen to avoid recomputing it
--wherever it's relevant in codegen.
seqE :: E -> Seq (T,[Name])
seqE = \case
  --integer literals may be at most one word
  EInteger n -> do
    let t = typeOfInteger n
    v <- pushK t (Const n)
    return (t,[v])
  --For now, it's either a function, local or undefined
  --locals can't shadow functions
  Var nm -> do
    ni <- getCNameInfo nm
    case ni of
      IsFunction t -> do
        v <- pushK t (LabelConst nm)
        return (t,[v])
      IsLocal t -> do
        --The number of words is determined by t... but it won't be a pure fun
        --once user-defined types are supported.
        n <- numWordsT t
        --For now, all vars in scope must also already be assigned, since they
        --enter scope on assignment.
        --A use of a var is not a noop, it's a renaming. The difference is
        --a subsequent assignment to the original var won't affect the
        --renamed one.
        ws <- sequence [copyVar (Word i t) (nm ++ "#" ++ show i)
                       | i <- [1..n]]
        return (t,ws)
      IsUnbound -> throwE $ UnboundVar nm
  --The fields are concatenated, with the field values emitted in reverse
  --order.
  EStruct padnmes -> buildStruct padnmes
  _ -> error "TODO"

--Given the IR vars to assign to a C local, emits the assignment.
--We assume the vars have the correct type.
--x = ws => x#1 : typeof w1 = copy w1 ..
assign :: Name -> [Name] -> Seq ()
assign x [] = return ()
assign x ws = do
  --If this pattern fails something's gone horribly wrong; the rhs doesn't
  --exist or 
  mt <- getIRVarType $ head ws
  case mt of
    Just (Word 1 t) -> 
      sequence_ [emitOp [(x ++ "#" ++ show n, Word n t)] Copy [w]
                | (n,w) <- zip [1..] ws]
    _ -> throwE $ BadFirstRHSInAssign x mt ws

--target type, source type, words of source value
--Supported coercion: any int -> int, any struct -> struct
{-Struct coercion scheme:
for nth field = name, t in target:
 if source has .name : t', result.name = source.name; break
 if source has nth field = __fieldN : t', result.name = source.__fieldN; break
 else result.name = all zeroes --constant sharing could be useful here

Note result.field = source.field also involves soft coercion
-}
softCoerce :: T -> T -> [Name] -> Seq [Name]
--When lengthening to a signed int, signextend
--When shortening any int, mask
--TODO: when it would shorten code sufficiently, replace mask with shl,shr
softCoerce target source ws
  | target == source = return ws
  | Int s1 len1 <- target,
    Int s2 len2 <- source,
    [w] <- ws =
      case () of
        _ | len1 < len2 -> runEDSLWord $ len1 `lowestBits` (EVar w)
          | len1 > len2, s1 ->
            runEDSLWord $ signextend (word $ fromIntegral len1) (EVar w)
          | let -> runEDSLWord $ coerce (Word 1 target) (EVar w)
  --For now, no general struct coercion, only tuple -> tuple
  --Scheme: for each field in target, softCoerce source field and then coerce
  --to tuple words.
  --Is it essential to actually modify the IR type? It's just a safety feature
  --to detect bugs in codegen... but it's worth it, I should be able to
  --optimize the copies away.
  | Just ts1 <- unTuple target, Just ts2 <- unTuple source =
    softCoerceTuple ts1 ts2 ws

unTuple :: T -> Maybe [T]
unTuple = \case
  Struct padnmts -> go 1 padnmts
  _ -> Nothing
  where go n ts =
          case ts of
            [] -> return []
            (pad,fieldN,t):ts
              | pad == WordPad, fieldN == "__field" ++ show n ->
                (t:) <$> go (n+1) ts

softCoerceTuple :: [T] -> [T] -> [Name] -> Seq [Name]
softCoerceTuple ts1 ts2 ws =
  case ts1 of
    [] -> return [] --coercing to an empty tuple
    t:ts1' ->
      case ts2 of
        --now the rest is all zeroes
        [] -> undefined

--The result of coercing 0 to any type t: all zeroes in the bitpattern.
--May not be a valid value of that type; use of e.g. null ptr may be UB.
--We do some free constant sharing here.
nullValue :: T -> Seq [Name]
nullValue t = do
  n <- numWordsT t
  map fst <$> runEDSL (do
    z <- word 0
    sequence [coerce (Word i t) (return z) | i <- [1..n]])
          
{-
--TODO update pkgs...
(!?) :: [a] -> Int -> Maybe a
[] !?  _ = Nothing
(x:xs) !? n
  | n == 0 = Just x
  | let = xs !? n
-}
                             
--The type of the struct is given by the padding, names and types of elements.
--Each word of the struct is the concatenation of slices of fields; the
--cheapest case is when the word contains a single unsliced field.
--Layout: the padded fields are placed rightmost in the struct, with the struct
--itself word-padded.
buildStruct :: [(Padding,Name,E)] -> Seq (T,[Name])
buildStruct padnmes = do
  padnmtws <- mapM (\(pad,nm,e) -> do
                       (t,ws) <- seqE e
                       return (pad,nm,t,ws)) padnmes
  let padnmts = map (\(pad,nm,t,_) -> (pad,nm,t)) padnmtws
      structType = Struct padnmts
  --For each field value, the words it consists of and the bitsize of the
  --padded field; that's all the information needed to determine the scheme
  --for computing the struct.
  --Note we reverse the words because we assemble the struct from the back!
  bszws <- mapM (\(pad,_,t,ws) -> do
                  bsz <- padWith pad <$> numBitsT t
                  return (bsz,reverse ws)) padnmtws
  wc <- numWordsT structType
  sws <- buildStructOps structType wc bszws
  return (structType,sws)
--Concat scheme:
--a ++ b = a << bitsizeof b | b
--Starting from the last field, concatenate the last 256b worth of field
--values into an anon var : Word n structType
--Skip 0-sized fields, they have no runtime effect - and should not constrain
--op ordering!
--When you cross a word boundary, you may have partially consumed a field;
--then you should right-shift the remainder.
--The offset of a field depends on previous fields; a word-sized field in
--front of a byte must be divided over two words.
{-Algo:
Compute the left-shift offset of each field word from the end of
the struct. Associate each word with a bitsize (always 256 for word-padded,
at least 1 for bit-padded).
For each word wc-k, include words where off..off+bitsize overlaps with
k*256.. k*256 + 255.
-}
buildStructOps :: T -> Int -> [(Int,[Name])] -> Seq [Name]
buildStructOps st wc bszwss =
  let shiftwss = structLayout bszwss
  in map fst <$> (mapM (buildStructWord st) $ zip [1..wc] shiftwss)
--st (n,[(16,a),(0,b)]) => a << 16 | b : Word n st
buildStructWord st (n,shiftws) = do
  let shifted = map (\case (shift,v)
                             | shift > 0 ->
                               shl (word $ fromIntegral shift) (EVar v)
                             | shift < 0 ->
                               shr (word $ fromIntegral $ negate shift) (EVar v)
                             | let -> EVar v) shiftws
      disjunction = coerce (Word n st) $ foldr1 (.|) shifted
  runEDSL disjunction
  
--field values (bitlen, words) -> [struct word recipe]
structLayout :: [(Int,[Name])] -> [[(Int,Name)]]
structLayout bszwss =
  let pwords = splitFields $ reverse $ map (\(bsz,ws) -> (bsz,reverse ws))bszwss
      pwordoffs = computeOffsets pwords
  in reverse $ map reverse $ divideIntoWords pwordoffs
--Given a bitsize and the reversed list of vars of a value, give each a
--bitlen (all but the last is 256).
splitIntoPartialWords :: (Int,[Name]) -> [(Int,Name)]
splitIntoPartialWords (bsz,ws) =
  case ws of
    [w] -> [(bsz,w)]
    w:ws -> (256,w) : splitIntoPartialWords (bsz-256,ws)
--Collect all field words into a list of partial words
splitFields :: [(Int,[Name])] -> [(Int,Name)]
splitFields = (>>= splitIntoPartialWords)
--bitlen, word => offset,bitlen,word
computeOffsets :: [(Int,Name)] -> [(Int,Int,Name)]
computeOffsets = computeOffsets' 0
computeOffsets' off = \case
  [] -> []
  (len,w) : lenws -> (off,len,w) : computeOffsets' (off+len) lenws
--Given a list of partial words, returns the composite words and shift values
--for each struct word (in reverse order)
divideIntoWords :: [(Int,Int,Name)] -> [[(Int,Name)]]
divideIntoWords = diw 0
  where
    --diw 0 generates the first struct word, diw 256 the second etc
    diw _ [] = []
    diw off offlenws =
      let (wordElems,offlenws') = takeBits off offlenws
      in wordElems : diw (off + 256) offlenws'
--Given a starting bit offset, a number of bits to take and a list of partial
--words, takes a prefix of the partial words and includes their shift values
--(may be negative).
takeBits :: Int -> [(Int,Int,Name)] -> ([(Int,Name)],[(Int,Int,Name)])
takeBits = takeBits' []
takeBits' accum off = \case
  --If the word overlaps with the range off..off+255, include it in accum
  --If it extends beyond, don't consume it and stop collecting words
  (o,l,w) : olws
    | o-off > 255 -> (reverse accum,(o,l,w):olws)
    | o-off+l > 255 -> (reverse $ (o-off,w) : accum, (o,l,w) : olws)
    | o-off+l >= 0 -> takeBits' ((o-off,w):accum) off olws
  [] -> (reverse accum,[])
  olws -> (reverse accum,olws)

--Since I'm now building complex exprs, a little DSL for that would be useful.
--Example: a << k1 | b << k2 | c : Word n struct
--Derive return types from argument types when running.
--Make it an Ecomp-style monad to enable sharing of internally returned vars.
type EVar = (Name,IRT)
--The creatively named Expression DSL
data EDSL a where
  --Use a var created outside, getting its type
  EVar :: Name -> EDSL EVar
  --Apply an operator to vars, getting one or more return vars
  --TODO change Maybe to Either SeqError?
  App :: Operator -> ([IRT] -> Maybe [IRT]) -> [EDSL EVar] ->  EDSL [EVar]
  (:>>=) :: EDSL a -> (a -> EDSL b) -> EDSL b
  EReturn :: a -> EDSL a
instance Functor EDSL where
  fmap f m = do
    x <- m
    return $ f x
instance Applicative EDSL where
  pure = return
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x
instance Monad EDSL where
  return = EReturn
  (>>=) = (:>>=)
instance MonadFail EDSL where
  fail = error
runEDSLWord :: Expr -> Seq [Name]
runEDSLWord e = runEDSL $ do
  (v,irt) <- e
  return [v]
runEDSL :: EDSL a -> Seq a
runEDSL = \case
  EVar nm -> do
    mt <- M.lookup nm <$> gets irLocalTypes
    case mt of
      Nothing -> throwE $ Couldn'tLookupVarTypeInEDSL nm
      Just t -> return (nm,t)
  App op ty arges -> do
    es <- mapM runEDSL arges
    let argts = map snd es
    case ty argts of
      Nothing -> throwE $ BadArgsInEDSL op es
      Just rets -> do
        --for each ret t in rets, alloc an anonymous var
        retvs <- mapM typedAnonVar rets
        emitOp retvs op (map fst es)
        return retvs
  m :>>= f -> runEDSL m >>= (runEDSL . f)
  EReturn x -> return x
typedAnonVar :: IRT -> Seq EVar
typedAnonVar irt = do
  v <- newAnonVar
  return (v,irt)

type Expr = EDSL EVar
word :: Integer -> Expr
word k = head <$> App (Push $ Const k) (\_ -> Just [tword]) []
tword = Word 1 (Int False 256)
--Coerces an arbitrary var to a var of another type; ignores kind so mem
--can be coerced to word and vice versa!
coerce :: IRT -> Expr -> Expr
coerce irt e = do
  [v] <- App Copy (\[_] -> Just [irt]) [e]
  return v
--Note: the shift value is the first argument, i.e. the top of the stack!
--That's the opposite order of << or >> in C.
shl :: Expr -> Expr -> Expr
shl = op2 "shl"
shr = op2 "shr"
(.|) = op2 "or"
op1 :: String -> Expr -> Expr
op1 opcode a = do
  [v] <- App (Opcode opcode) (\case [Word{}] -> Just [tword]
                                    _ -> Nothing) [a]
  return v
op2 :: String -> Expr -> Expr -> Expr
op2 opcode a b = do
  [v] <- App (Opcode opcode) (\case
                                [Word {}, Word {}] -> Just [tword]
                                _ -> Nothing) [a,b]
  return v
--What is the correct arg order...? TODO find out
signextend :: Expr -> Expr -> Expr
signextend = op2 "signextend"

--Using mask rather than shl, shr
lowestBits :: Int -> Expr -> Expr
lowestBits len e = op2 "and" (word $ 2 ^ len - 1) e
--I have copies all over the place... will not SSAing between SLCs make them
--less efficient?
--Consider (x,f(),x); use fields of tuple.
{-That becomes
a1 = x
a2 = call f(ret) --SLC boundary
ret:
a3 = x
...use a1,a2,a3
Yes, because a1 is live it must be represented at the end of the calling SLC.
But by extending the state to include renamings (thus storing multiple vars
in one word on the stack), I can get around that.
Perhaps I could get phi functions and thus full SSA by making
xN = slot(n) my phi substitute.
while e body =>
outvars = phi(outvars,invars)
It's only applicable if the while breaks.
Phi functions are just noops establishing a dependency.
-}

--Copy an IR var to a new anon var; may become a dup after SSA
--Why a type param? Because the type of the copied word may change, e.g.
--if you create a tuple (w1,w2,w3) in which case copies will be
--Word 1,2,3 of a tuple rather than a uint256.
--Another example: zero-cost coercion, such as uint8 to uint256
copyVar :: IRT -> Name -> Seq Name
copyVar irt nm = do
  mt <- getIRVarType nm
  case mt of
    Nothing -> throwE $ Can'tCopyUnboundIRVar nm
    Just t -> do
      v <- newAnonVar
      emitOp [(v,irt)] Copy [nm]
      return v
--push a static one-word C type
pushK :: T -> StaticValue -> Seq Name
pushK t sv = do
  v <- newAnonVar
  emitOp [(v,Word 1 t)] (Push sv) []
  return v

emit :: IR -> Seq ()
emit ir = tell [ir]
--If the lhs vars are new, binds them to their type
--If a var v already exists, checks its type matches and errors otherwise
--Repeated vars in the lhs cause an error
--All vars in the rhs must be bound
--Returns the lhs vars
emitOp :: [(Name,IRT)] -> Operator -> [Name] -> Seq [Name]
emitOp nmts op args = do
  typeCheckLHS nmts
  sequence_ [do mt <- getIRVarType arg
                case mt of
                  Nothing -> throwE $ UnboundVarInOpRHS arg nmts op args
                  Just _ -> return ()
            | arg <- args]
  emit $ nmts IR1.:= (op,args)
  return $ map fst nmts
typeCheckLHS :: [(Name,IRT)] -> Seq ()
typeCheckLHS = typeCheckLHS' S.empty
typeCheckLHS' :: Set Name -> [(Name,IRT)] -> Seq ()
typeCheckLHS' nms = \case
  [] -> return ()
  (nm,t):nmts ->
    if S.member nm nms
    then throwE $ DuplicateVarsInLHS nm nms
    else do
      mirt <- getIRVarType nm
      case mirt of
        Just t'
          | t' == t -> return ()
          | let -> throwE $ IlltypedLHS nm t t'
        Nothing -> putIRVarType nm t
      typeCheckLHS' (S.insert nm nms) nmts
--Nothing indicates unbound
getIRVarType :: Name -> Seq (Maybe IRT)
getIRVarType nm = M.lookup nm <$> gets irLocalTypes
putIRVarType :: Name -> IRT -> Seq ()
putIRVarType nm t = do
  s <- get
  put s{irLocalTypes = M.insert nm t $ irLocalTypes s}

newAnonVar :: Seq Name
newAnonVar = do
  s <- get
  let n = anonVarCounter s
  put s{anonVarCounter = n+1}
  return $ "$anon" ++ show n

--TODO deduplicate...
--(Word) (-1) becomes signextend 0xff, but that's fine: you can just constant
--expand it or replace with 0 - 1.
typeOfInteger :: Integer -> T
typeOfInteger n =
  Int (n < 0) --it's signed iff it's negative
  (min 256 $ 8 * (byteLen $ abs n))
  where byteLen 0 = 0
        byteLen n = 1 + byteLen (n `div` 256)

data NameInfo = IsFunction T
              | IsLocal T
              | IsUnbound
  deriving (Eq,Ord,Read,Show)
getCNameInfo :: Name -> Seq NameInfo
getCNameInfo nm = do
  mod <- askModule
  case M.lookup nm $ defuns mod of
    Just (Defun _ t _ _) -> return $ IsFunction t
    _ -> do
      lts <- gets cLocalTypes
      case M.lookup nm lts of
        Just t -> return $ IsLocal t
        _ -> return IsUnbound

--TODO deduplicate
--This'll become dependent on mod once user-defined types are introduced
numWordsT :: T -> Seq Int
numWordsT t = do
  n <- numBitsT t
  return $ (padTo 256 n) `div` 256
numBitsT :: T -> Seq Int
numBitsT = \case
  Int _ n -> return n
  a :-> b -> return 16
  Struct padnmts ->
     sum <$> mapM (\(pad,_,t) -> padWith pad <$> numBitsT t) padnmts

padWith pad = padTo (case pad of
                       BitPad -> 1
                       BytePad -> 8
                       WordPad -> 256)
padTo n m = n * ((if m `mod` n == 0
                  then 0
                  else 1) + (m `div` n))

--I need to type check at the same time...
--integer literals become the smallest type that fits; limit to 256b
--they become signed iff they're negative.
--Var is either a local or a function; disallow placement of primfuns.
--f :$ x is either a function or primfun application
--structs may be multiple words, and is formed via shift and or of its
--underlying words. Tuples can be optimized.
