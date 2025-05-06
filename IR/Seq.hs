module IR.Seq where

--The definition and basic API of the Seq monad, which is used to convert
--AST function definitions into a SEQuence of IR instructions (hence the
--name).

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

--The errors that can be produced during codegen.
--Once I move the pre-codegen stages out of the SeqError type
--and move type inference out of Seq, many of these will no longer be used;
--TODO remove them.
data SeqError = UnboundVar Name
              --The stuff that can go wrong in an op
              | IlltypedLHS Name IRT IRT
              | DuplicateVarsInLHS Name (Set Name)
              | Can'tCopyUnboundIRVar Name
              | UnboundVarInOpRHS Name [(Name,IRT)] Operator [Name]

              | Couldn'tLookupVarTypeInEDSL Name
              | BadArgsInEDSL Operator [EVar]
              | BadFirstRHSInAssign Name (Maybe IRT) [Name]
              --C-level type errors
              | BadFunctionType Name T
              | Can'tAssignToFunction Name
              | Can'tAssignToPrimFun Name --it's useful to distinguish
              | ApplicationToNonFunction E T
              | BadArgInTruthy [Name]
              | BadArgPrimFun Name T
              --Errors from pattern matching
              | PTupNonTuple [Pat] T
              | PTupLengthMismatch [Pat] [T]
              --Type synonym errors
              | TySynsShadowPrimTySyns (Set Name)
              --Innovation: a single constructor for locating errors,
              --structuring the error type into context-specific types
              | InTySyn Name InTySynErr
              --The error below isn't really specific to one syn...
              | FoundTySynCycle [Name]
              | UnderAppliedSynInDefun Name [T]
              --Substituting
              | ArgsAppliedToStructInDefun [Field T] [T]
              --A placeholder error to avoid having to add new error types
              --constantly while developing
              | GenericError String
  deriving (Eq,Ord,Read,Show)
data InTySynErr = TyConOOS Name | TyVarOOS Name | TySynRepeatedArgs [Name]
  | UnderAppliedSyn Name | ArgsAppliedToStruct [Field T]
  deriving (Eq,Ord,Read,Show)
