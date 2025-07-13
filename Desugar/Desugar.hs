{-# LANGUAGE LambdaCase, StandaloneDeriving, DeriveDataTypeable #-}
module Desugar.Desugar where
--A separate module for desugaring; Compiler should just tie each stage
--together and handle the IO.

import Util (complainIf,(?))
--import E.Par (pM,myLexer)
--import E.ErrM (Err(..))
import E.Abs (Ident(..),UIdent(..))
import qualified E.Abs as P

--CST -> AST
import AST.DTs
import AST.Util (rollTyApps)
import Desugar.DTs
import Desugar.T (desugarT)
import Desugar.Datatypes (processDTs)
--AST -> AST

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Trans.Except
import Control.Monad.State
import Text.Read (readMaybe)
import Data.List (sort)
import Data.Char (ord) --for string desugaring
import Control.Arrow ((***))
import Data.Maybe (fromMaybe)

import Data.Generics (Data(..),everything,mkQ,everywhere,mkT)

--Declarations are order-independent, modulo the static names allocated to
--strings (which should be irrelevant to compilation if it's successful).
{-
desugar :: P.M -> Either DError Module
desugar (P.Module ds) =
  case runState (runExceptT $ mapM_ desugarD ds) emptyModule of
    (Left derr, _) -> Left derr
    (Right (), m) -> Right m
emptyModule =
  Module {
  tysigs = M.empty,
  kindsigs = M.empty,
  kinds = S.empty,
  defaults = M.empty,
  defuns = M.empty,
  tysyns = M.empty,
  --static = M.empty,
  globals = M.empty,
  dtsInfo = M.empty,
  --datatypeRegions = M.empty,
  --constructors = M.empty,
  --fieldTypes = M.empty,
  --fieldSpecs = M.empty,
  anonStaticCtr = 0
  }
-}

type De = ExceptT DError (State Module)

--Grouping declarations by constructor first leads to cleaner code, as I can
--get an overview of the handling for each decl type in one place.
--General principle: doing a task all at once in its own traversal is
--clearer and less bug-prone than the alternative (interspersing it with other
--code and maintaining invariants that ensures doing so is valid).
--It also lets me do more in Desugar since I can process decl types separately;
--in particular, it lets me desugar g => *g because I gather all globals first.
--I can also use minimal monad capabilities, reducing the risk of bugs.
--What do I need to do? Allocate new names in let bindings and new globals
--for strings; throw errors.
--That just requires StateT Int (Except err), where err can now be specific
--to each step.

--Groups elements of a showable datatype by top-level constructor.
--Precondition: it has no infix constructors...
--It's hacky and inefficient but simple.
--Unintended consequence: duplicate identical declarations are ignored.
--That's fine?
--Note it's no problem the order of decls is reversed since they should be
--order-independent anyway.
groupByCon :: Show a => [a] -> Map String [a]
groupByCon as =
  let kas = [(head $ words $ show a, a) | a <- as]
      empty = M.fromSet (const []) $ S.fromList $ words
        "Default Defun Instance TySig KindSig TySyn Import Global Data Tag"
  in foldr (\(k,a) m -> M.adjust (a:) k m) empty kas

--New desugar algo:
--First group decls by constructor
--Group each type of decl by its key; error on internal duplicates
-- defuns and instances are grouped together and are mutex
--Error on external duplicates:
--Dyn lowercase names: funs, vars
--Dyn uppercase: constructors
--Static (uppercase only): datatypes, tysyns, kinds
desugar2 :: P.M -> Either DError Module
desugar2 (P.Module ds) = do
  let nm2d = groupByCon ds
  --Four types need be desugared: STEP (S, T, E, Pat)
  --T can be desugared independently, but E desugaring relies on context
  --(and consequently S and Pat which contain Es do as well).
  --The context required is:
  --1) the global set (used for g=>*g in P,E)
  --2) boxed field status (used for bdt.field => *(...).fieldStructCon in E)
  --3) a string numbering m (used for "str" => *($string++show m["str"]))
  
  --globals
  gs <- groupGlobals nm2d
  --data
  dts <- groupEx "Data" (\(P.Data ca rhs) ->
                           let (nm,args) = desugarConArgs ca
                           in (nm,(args,rhs))) nm2d
  tags <- groupEx "Tag" (\(P.Tag ca pt contags) ->
                           let (nm,args) = desugarConArgs ca
                               t = desugarT pt
                               con2e = M.fromList $
                                 map (\(P.ConTag (UIdent con) pe) ->
                                        (con,pe)) contags
                           in (nm,(args,t,con2e)))  nm2d
  dtsFull <- processDTs dts tags --Now we have 1)
  
  let gset = M.keysSet gs --Now we have 2)
      fset = M.keysSet dis
  --To get the string numbering we need to collect the set of all string
  --literals in the source. That can be done cleanly by running an everything
  --on nm2d (which contains every decl).
  let strings = everything S.union (mkQ $ \case
                                       P.String str -> S.singleton str
                                       _ -> S.empty) nm2d
      string2n = M.fromList $ zip (S.toList strings) [1..]
  --Now we have 3) and can define the SEP desugaring functions to use
      
  --Group all decl types by key
  --default
  dflts <- groupEx "Default" (\(P.Default (UIdent nm) t) -> (nm, desugarT t))
    nm2d
  --defun
  ds <- groupDefuns nm2d
  --instance
  let is = groupInstances $ nm2d M.! "Instance"
  dis <- combineDefsAndInstances ds is
  --tysig
  tsigs <- groupEx "Tysig" (\(P.TySig (Ident nm) t) -> (nm, desugarT t)) nm2d
  --kindsig
  ksigs <- groupEx "KindSig" (\(P.KindSig (UIdent nm) t) -> (nm, desugarT t))
    nm2d
  --tysyn
  tsyns <- groupEx "TySyn" (\(P.TySyn ca t) ->
                              let (nm,args) = desugarConArgs ca
                              in (nm,(args, desugarT t))) nm2d
  --Require:
  --No overlap between funs and globals
  --No overlap between datatypes, tysyns and kinds
  --All classes must have a signature
  --All type signatures must correspond to a fun or global
  
  --Expr desugaring
  --g => *g and string => g are simplest; they can be done on P.E without
  --issue. Indeed, doing so avoids defining it for both Pat and E.
  --Note this is done before substituting pointers for new globals
  let gs' = g2starg gset gs
      ds' = g2starg gset ds
  error "todo"
  
--Desugars global g to *g (where g is now considered a pointer)
g2starg :: Data d => Set Name -> d -> d
g2starg gset = everywhere $ mkT $ \case
  P.Var (Ident nm) | S.member nm gset -> P.Deref $ P.Var $ Ident nm
  e -> e
--Converts strings to array literals
--Desugarings:
--g => *g (stateless, can be done on either E or P.E)
--"abc" => &newg where code newg = array(97,98,99)
-- Content-based string var naming would make the pretty output unreadable...
-- instead number them.
-- 1. Collect the set of strings, then number them.
-- 2. Create the string global set
-- 3. Substitute the strings for their corresponding globals (not &g).
--It's simpler to do on E.
--Don't apply & to the string global... that way ! can be applied to str
--directly, and it can be efficiently copied using *ptr = "foo".
--Ah... then I don't need a global, I can convert to array(1,2,3) directly.
--Arrays which ultimately never touch the stack should just be *copied.

--p += k, p++ => let-bind exprs in p, reuse same location
--Issue: I also want to convert P.E to E, and that may fail
--It's awkward to operate on the CST, but the AST E should not have the
--features being desugared away - that's the whole point!
--That means I must choose between operating on the CST, adding undesired
--constructs to E or merging all desugaring steps into a single CST -> AST jump.
--Long-term solution: first convert to an intermediate AST?
--Con form standardization: Con {field: p} for patterns, fully applied Con
--for exprs.
--bdt.field => *(...).field' in exprs
--Pattern decomposition is deferred until after monomorphization, but the
--supporting tag and struct datatypes must be allocated here.
--I need to do that before bdt.field => *... because tagDT is a field!
--For boxed datatypes, tagDT is special in that it becomes a desugar of
--a tag pointer rather than a generated struct.

--Only defuns and globals contain exprs; they must be desugared.
--That involves allocating new code globals for strings and locals for
--let-based desugaring.
--It's clearer to do that only on the two relevant fields...
--But first, the un-desugared decls must be grouped.
--TODO: display all collisions and the associated definitions.

--DError-specific function
groupEx :: String -> (P.D -> (Name,v)) -> Map String [P.D] ->
  Either DError (Map Name v)
groupEx decltype sel decls =
  let ds = decls M.! decltype
  in groupExclusive sel ds ? Duplicate decltype
--Generic function
groupExclusive :: Ord k => (a -> (k,v)) -> [a] -> Either k (Map k v)
groupExclusive sel =
  foldM (\m a -> do
           let (k,v) = sel a
           complainIf (M.member k m) k
           return $ M.insert k v m) M.empty
  
--groupGlobals :: [P.D] -> Either Name (Map Name (Region, Maybe P.E))
groupGlobals = groupEx "Global " $
  \(P.Global gr vb) ->
    let (g,me) = collectVarBind vb
        r = desugarRegion gr
    in (g,(r,me))
--groupDefuns :: [P.D] -> Either Name (Map Name (P.E,P.S))
groupDefuns = groupEx "Defun" $
  \(P.Defun (Ident f) pe ps) -> (f,(pe,ps))

--Instances are keyed by function name; it's fine for there to be multiple
--instances for a single name, they're just collected into a set.
--groupInstances is pure because it can't fail.
groupInstances :: [P.D] -> Map Name (Set (P.T,P.E,P.S))
groupInstances ds =
  let kelems = [(fnm,(t,e,s)) | P.Instance (Ident fnm) t e s <- ds]
  in foldr (\(k,elem) m ->
              case M.lookup k m of
                Nothing -> M.insert k (S.singleton elem) m
                Just elems -> M.insert k (S.insert elem elems) m)
     M.empty kelems
--Combine ordinary defuns and instances into a single map; they're mutex, so
--complain if their fnames intersect.
combineDefsAndInstances :: Map Name (P.E,P.S) ->
                           Map Name (Set (P.T,P.E,P.S)) ->
                           Either DError (Map Name
                                         (Either (P.E,P.S)
                                          (Set (P.T,P.E,P.S))))
combineDefsAndInstances ds is = do
  let fds = M.keysSet ds
      fis = M.keysSet is
      conflicts = S.intersection fds fis
  complainIf (not $ S.null conflicts)
    $ DefunInstanceOverlap conflicts
  return $ M.union (M.map Left ds) (M.map Right is)
  
collectVarBind :: P.VarBind -> (Name, Maybe P.E)
collectVarBind = \case
  P.JustVar (Ident v) -> (v, Nothing)
  P.VarIs (Ident v) e -> (v, Just e)
  
desugarRegion :: P.GlobalRegion -> Region
desugarRegion = read . take 2 . show
  
desugarD :: P.D -> De ()
desugarD = error "to remove"
{-
desugarD = \case
  P.Defun (Ident f) lhs ps -> do
    checkForDuplicates f
    --Note patterns are a subset of syntactically valid Es
    p <- desugarP lhs
    --Need to add do block support to DTs?
    s <- desugarS ps
    modify (\m->m{defuns=M.insert f (p,s) $ defuns m})
  P.TySig (Ident f) pt ->
    addSig f pt tysigs (\x m -> m{tysigs=x}) DuplicateTySigs
  --Now tycons can either be level 1 (a la Memory, Word)
  --or level 2 (a la Region, Type).
  --Top-level kinds (level 2) can only be declared as Tycon : Kind
  --While they could in theory live in different namespaces, we instead check
  --that level-1 tycons don't collide with level-2 and vice versa.
  P.KindSig (UIdent tycon) pk -> do
    let k = desugarT pk
    ksigs <- gets kindsigs
    srts <- gets sorts
    --TODO add more informative error message
    complainIf (S.member tycon $ S.union srts $ M.keysSet ksigs)
      $ DuplicateKindSigs tycon
    if k == TyCon "Kind"
      then modify(\m->m{sorts = S.insert tycon srts})
      else modify(\m->m{kindsigs = M.insert tycon k ksigs})
  --Declares the default value for tyvars of kind k; duplicate defaults is a
  --desugar error.
  P.Default (UIdent k) pt -> do
    let t = desugarT pt
    ds <- gets defaults
    complainIf (M.member k ds)
      $ DuplicateDefaults k
    modify (\m->m{defaults = M.insert k t ds})
  P.TySyn conargs te -> do
    let (nm,args) = desugarConArgs conargs
    let t = desugarT te
    modify (\m -> m{tysyns = M.insert nm (args,t) $ tysyns m})
  P.Import mnm -> throwE $ UnresolvedImport mnm
  --Decision: fixed-size arrays are now a first-class type; array globals no
  --longer decay to pointers.
  --arr[len > 65536] needn't be caught... it's fine if it's an array of ()!
  P.Global pr varBind -> do
    (x,me) <- desugarVarBind varBind
    checkForDuplicates x
    let r = read $ take 2 $ show pr
    modify (\m->m{globals = M.insert x (r,me) $ globals m})
  --Relevant:
  --datatypes: params, conDecls
  --datatypeRegions: if Just r <- mr insert it
  --constructors: con : arg1 -> arg2 -> ... -> tycon params
  --fieldTypes: tycon params -> argN
  --fieldSpecs: con, n
  P.Data conArgs dataRHS -> do
    let (tycon,args) = desugarConArgs conArgs
        (condecls,mr) = desugarDataRHS dataRHS
    checkForDupTyCon tycon
    --Insert datatype entry
    modify (\m->m{datatypes = M.insert tycon (args,condecls) $
                 datatypes m})
    --If Just r <- mr insert it
    case mr of
      Just r -> modify (\m->m{datatypeRegions = M.insert tycon r $
                               datatypeRegions m})
      Nothing -> return ()
    --Add type signatures for constructors
    --TODO move them to tysigs instead? Need to check they're not underapplied,
    --so they should be treated differently. But for that I only need arity...
    let rett :: T --the return type of constructors
        rett = foldl (:$$) (TyCon tycon) $ map TyVar args
    let conArgs :: [(Name,[T])]
        conArgs = map (id *** (\case Left ts -> ts; Right nmts -> map snd nmts))
                  condecls
        conTs :: [(Name,T)]
        conTs = map (id *** (foldr (:->) rett)) conArgs
    mapM_ (\(con,t) -> do
              checkForDuplicates con
              modify (\m->m{constructors=M.insert con t $ constructors m}))
      conTs
    --Insert field types
    let conFields :: [(Name,Name,Int,T)] --(con,field nm,index,field type)
        conFields = do
          (con,ei) <- condecls
          case ei of
            Left _ -> [] --no fields
            Right nmts -> do
              (ix,(nm,t)) <- zip [0..] nmts
              return (con,'.':nm,ix,t)
    mapM_ (\(con,nm,ix,t) -> do
              s <- get
              let fts = fieldTypes s
              complainIf (M.member nm fts)
                $ DuplicateFieldNames nm
              put s{fieldTypes = M.insert nm (rett :-> t) fts,
                    fieldSpecs = M.insert nm (con,ix) $ fieldSpecs s}
          )
      conFields
-}
      {-
  P.StaticData (Ident nm) pe -> do
    checkForDuplicates nm
    e <- desugarE pe
    modify (\m->m{static=M.insert nm e $ static m})-}
    

desugarDataRHS :: P.DataRHS -> ([ConDecl],Maybe Name)
desugarDataRHS = \case
  P.Unboxed urhs ->
    let cons = desugarUnboxedRHS urhs
    in (cons,Nothing)
  P.Boxed urhs (Ident r) ->
    let cons = desugarUnboxedRHS urhs
    in (cons, Just r)
desugarUnboxedRHS :: P.UnboxedRHS -> [ConDecl]
desugarUnboxedRHS (P.URHS dcs) = map desugarDataCon dcs
desugarDataCon :: P.DataCon -> ConDecl
desugarDataCon = error "todo"
{-
desugarDataCon = \case
  P.DCArgs dca ->
    let (con,ts) = desugarDCA dca
    in (con, Left ts)
  P.DCRecord (UIdent con) rfs ->
    let nmts = map desugarRecordField rfs
    in (con, Right nmts)
-}
desugarDCA :: P.DCA -> (Name,[T])
desugarDCA = \case
  P.DCANil (UIdent con) -> (con,[])
  P.DCACons dca pt ->
    let t = desugarT pt
        (con,ts) = desugarDCA dca
    in (con,ts ++ [t])
desugarRecordField :: P.RecordField -> (Name,T)
desugarRecordField (P.RF (Ident nm) pt) = (nm,desugarT pt)

addSig :: Name -> P.T ->
          (Module -> Map Name T) ->
          (Map Name T -> Module -> Module) ->
          (Name -> DError) ->
          De ()
addSig nm pt getField setField err = do
    let t = desugarT pt
    map <- gets getField
    complainIf (M.member nm map)
      $ err nm
    modify $ setField $ M.insert nm t map
{-
  P.Data lhs rhs -> do
  --Duplicate params, duplicate constructors and free tyvars in arg types to
  --be caught in IR1
  --It's also not necessary to check params don't shadow non-type names;
  --they live in different namespaces.
  let (tycon,params) = desugarConLHS lhs
  conmts <- desugarConRHS (tycon,params) rhs
  checkForDuplicates tycon
  --We don't actually need to prevent collisions between constructors in
  --different datatypes, or between constructors and tysyns!
  --That's because the alloc ptr var gives you all the type info you need
  --on construction,
  --and e gives you a monomorphic type in case e of {...}.
  s <- get
  put s{datatypes = M.insert tycon (params,conmts) $ datatypes s}
  desugarDs rest
--Enums are currently 8b by default and have values 0..|ecs|-1.
--Ways enum can fail:
--tycon or member collision with existing value;
--duplicate member names;
-- >256 constructors
desugarDs ((P.Enum (UIdent tycon) ecs):rest) = do
  let nms = map (\(P.EC (Ident nm)) -> nm) ecs
  if length nms > 256
    then throwE MoreThan256EnumNamesInOneEnum
    else return ()
  case filter ((>1) . snd) $ count nms of
    (nm,_):_ -> throwE $ DuplicateEnumName tycon nm
    _ -> return ()
  checkForDuplicates tycon
  mapM_ checkForDuplicates nms
  s <- get
  put s{enums = M.insert tycon nms $ enums s,
        enumValues = M.union (M.fromList [(nm,(tycon,i))
                                         | (nm,i) <- zip nms [0..]])
                     $ enumValues s
       }
  desugarDs rest
desugarDs (P.StaticData pt (Ident nm) pe : rest) = do
  let t = desugarT pt
  e <- desugarE pe
  handleStaticData t nm e
  desugarDs rest
desugarDs (P.StaticDatatype pt (Ident nm) pe : rest) = do
  let t = desugarT pt
  e <- desugarE pe
  handleStaticDatatype t nm e
  desugarDs rest
desugarDs other = throwE $ BadDOrdering other
-}

count :: Ord a => [a] -> [(a,Int)]
count as =
  case sort as of
    [] -> []
    a:as' -> go a 1 as'
      where go a n = \case
              [] -> [(a,n)]
              a':as
                | a == a' -> go a (n+1) as
                | let -> (a,n) : go a' 1 as

--This can't fail, so there's no need to make it a monad
desugarConArgs :: P.ConArgs -> (Name,[Name])
desugarConArgs = go
  where go = \case
          P.CANil (UIdent tycon) -> (tycon,[])
          P.CACons conlhs (Ident param) ->
            let (tycon,params) = go conlhs
            in (tycon,params++[param]) --I know it's quadratic...

--This can fail because I use E for the constructors; todo make the BNFC
--syntax more restrictive so I don't need a bunch of unnecessary parentheses
--to get it to parse right...
--Now takes (tycon,params) in order to add each con to constructors with its
--type.
--TODO change to (Name,Name,[Name]) to reflect the fact that the param list
--will always be nonempty.
--Problem: I'm determining the tags in the desugaring phase!
--Maybe I should instead refer to a scheme for determining them, to be
--resolved in IR.
{-
desugarConRHS :: (Name,[Name]) -> [P.DataCon] -> De [(Name,T)]
desugarConRHS (tycon,r:params) cons =
  mapM (\(tag,(P.DC (UIdent con) parg)) -> do
           let arg = desugarT parg
           addConstructor con (tag,arg,tycon,r,params)
           return (con,arg)
       ) $ zip [0..] cons
-}

{-
--Adds the info of a new constructor to the constructors map; throws an error
--if there's a duplicate. Constructors do not conflict with tysyns or tycons.
addConstructor :: Name -> T -> De ()
addConstructor con t = do
  checkForDuplicates con
  error "todo"
-}

{-
--The check for duplicate names for dynamic values; datatypes and tysyns have
--their own namespace.
--Potential opt: split check for lowercase names and constructors
checkForDuplicates :: Name -> De ()
checkForDuplicates nm = do
  m <- get
  --TODO give a more informative error message
  complainIf (S.member nm $ S.unions $
              [M.keysSet $ defuns m,
               --M.keysSet $ static m,
               M.keysSet $ globals m,
               M.keysSet $ constructors m
              ])
    $ DuplicateDeclsForName nm
-}
--Kind signatures render hardcoded prim tycons unnecessary!
--But they also mean datatypes may be mentioned twice: once in a kind
--signature and once in a data decl.
--So when desugaring a kind signature, one must check the kind signature map
--but not this function.
checkForDupTyCon :: Name -> De ()
checkForDupTyCon nm = error "todo remove" {-do
  m <- get
  complainIf (S.member nm $ S.unions $
              [M.keysSet $ tysyns m,
               M.keysSet $ datatypes m
              ])
    $ DuplicateTyCons nm-}


{-
--The syntax ensures ordering: [wordpad] [wordalign] (fnm: t | t)
desugarFieldT :: P.TField -> Field T
desugarFieldT = go1
  where go1 = \case
          P.TPad fld -> go2 Word fld
          P.TF1 fld -> go2 Byte fld
        go2 pad = \case
          P.TAlign fld -> go3 pad Word fld
          P.TF2 fld -> go3 pad Byte fld
        go3 pad al = \case
          P.TNamed (Ident nm) pt ->
            ((pad,al),Just nm,desugarT pt)
          P.TAnon pt ->
            ((pad,al),Nothing,desugarT pt)
-}
{-
p ::=
_, x, *e, p.field, p!e, e[e], Con args, Con {field: p}
-}
desugarP :: P.E -> De Pat
--desugarP = desugarE
desugarP = go
  where go = \case
          P.EmptyTuple -> return $ PConArgs "Unit" []
          P.Tuple p ps ->
            foldr (\p1 p2 -> PConArgs "Pair" [p1,p2]) (PCon "Unit" [])
            <$> mapM go (p:ps)
          P.Var (Ident nm) -> return $ PVar nm
          P.Wild -> return PWild
          --ptr[ix] => *(indexPtr (ptr,ix))
          P.Index pptr pix -> do
            ptr <- desugarE pptr
            ix <- desugarE pix
            return $ Deref $ Var "indexPtr" :$ (Var "Pair" :$ ptr :$
                                                (Var "Pair" :$ ix :$
                                                 Var "Unit"))
          P.Dot p (Ident nm) -> (:.) <$> go p <*> return nm
          P.Bang pp pe -> (:!) <$> go pp <*> desugarE pe
          P.Deref e -> Deref <$> desugarE e
          P.Con (UIdent con) -> return $ PConArgs con []
          P.ConRecord (UIdent con) fields -> do
            nmps <- mapM desugarFieldP fields
            return $ PCon con nmps
          --All applications in pat must be of the form Con ps
          P.App pf px -> do
            let (conp,args) = unroll [px] pf
                unroll pes = \case
                  P.App pf px -> unroll (px:pes) pf
                  pe -> (pe,reverse pes)
            case conp of
              P.Con (UIdent con) -> do
                ps <- mapM desugarP args
                return $ PConArgs con ps
              _ -> throwE $ MalformedPattern $ P.App pf px
          pe -> throwE $ MalformedPattern pe
        todo = error "todo"        

desugarFieldP :: P.EField -> De (Name, Pat)
desugarFieldP (P.EField (Ident nm) pp) = ((,) nm) <$> desugarP pp

desugarS :: P.S -> De S
desugarS = \case
  P.SE e -> SE <$> desugarE e
  P.If e th el -> Ifte <$> desugarE e <*> desugarS th <*> desugarS el
  P.While e body -> While <$> desugarE e <*> desugarS body
  P.Return e -> Return <$> desugarE e
  P.Do ss -> Block <$> mapM desugarS ss
  P.Case pe pcases -> do
    e <- desugarE pe
    cases <- mapM desugarCase pcases
    return $ Case e cases
  P.Break -> return Break
  P.Continue -> return Continue
  --for (start;cond;each) s => {start;while (cond) {s;each}}
  P.For {} -> error "todo for loops"
  P.Declare varBinds ->
    Declare <$> mapM (((id *** fromMaybe (Var "null" :$ Var "Unit"))<$>) .
                      desugarVarBind) varBinds

desugarVarBind :: P.VarBind -> De (Name, Maybe E)
desugarVarBind = \case
  P.JustVar (Ident nm) -> return (nm, Nothing)
  P.VarIs (Ident nm) pe -> ((,)nm) <$> Just <$> desugarE pe

--TODO allow _, x patterns in case
desugarCase :: P.CASE -> De (Pat,S)
desugarCase (P.C pe ps) = do
  p <- desugarP pe
  s <- desugarS ps
  return (p,s)

--Can desugarE throw any errors?
desugarE :: DInfo -> P.E -> E
desugarE = error "todo"
{-
desugarE = go
  where go = \case
          P.EmptyTuple -> return $ Var "Unit"
          P.Tuple pe pes -> tupleE <$> mapM go (pe:pes)
          --Integers are sugar for fromWord #w, where w is :: Word;
          --all overloading is implemented via function application under the
          --hood.
          P.HexInt (P.HexInteger str) -> go $ P.Int $ read str
          P.Int n -> return $ po1 "fromWord" $ EInteger n
          P.Var (Ident nm) -> return $ Var nm
          P.String str -> handleString str
          P.Con (UIdent nm) -> return $ Var nm
          --Patterns are now exprs...
          P.Wild -> return $ Var "_"
          --The pattern decomposition pass needs verbatim _++ and _-- repr
          --because we don't yet know which vars are globals.
          P.PlusPlusPost pp -> PPPost <$> desugarP pp
          P.MinusMinusPost pp -> MMPost <$> desugarP pp
          --indexPtr must take the ptr as its first argument to preserve eval
          --order.
          P.Index pptr pix -> do
            ptr <- go pptr
            ix <- go pix
            return $ po1 "deref" $ po2 "indexPtr" ptr ix
          P.Dot e (Ident nm) -> op1 ('.' : nm) e
          P.Arrow pe (Ident nm) -> do
            e <- go pe
            return $ po1 ('.':nm) $ po1 "deref" e
          --I use array (e1,e2,...) as hacky syntax for array exprs
          P.App (P.Var (Ident "array")) ptup -> do
            tup <- go ptup
            case unTupleE tup of
              Just es -> return $ EArray es
              Nothing ->
                throwE $ GenericDError "Non-tuple passed to array 'function'"
          P.App pf px -> (:$) <$> go pf <*> go px
          P.PlusPlusPre p -> PPPre <$> desugarP p
          P.MinusMinusPre p -> MMPre <$> desugarP p
          P.Negate a -> op1 "negate" a
          P.Not a -> op1 "lNot" a
          P.BitwiseNot a -> op1 "bwNot" a
          P.Deref a -> op1 "deref" a
          P.AddressOf a -> op1 "ampersand" a
          P.Mul a b -> op2 "multiply" a b
          P.Div a b -> op2 "divide" a b
          P.Mod a b -> op2 "modulo" a b
          P.Plus a b -> op2 "plus" a b
          P.Minus a b -> op2 "minus" a b
          P.Shl a b -> op2 "shL" a b
          P.Shr a b -> op2 "shR" a b
          P.MyLT a b -> op2 "lt_" a b
          P.LTE a b -> op2 "lte_" a b
          P.MyGT a b -> op2 "gt_" a b
          P.GTE a b -> op2 "gte_" a b
          P.Eq a b -> op2 "eq_" a b
          P.NEq a b -> op2 "neq_" a b
          P.BitwiseAnd a b -> op2 "bwAnd" a b
          P.BitwiseXor a b -> op2 "bwXor" a b
          P.BitwiseOr a b -> op2 "bwOr" a b
          P.And a b -> op2 "scAnd" a b
          P.Or a b -> op2 "scOr" a b
          --Problem: a may be *expensiveExpr
          -- += et al should only be applicable to infallible patterns
          --(i.e. not Con)
          -- *e += 1 should compute the address once
          P.Assign a aop b -> do
            ap <- desugarP a
            a' <- go a
            b' <- go b
            return $ ap := aop2op aop a' b'
          --Coerce need no longer be part of the syntax
          P.TypeAnnot pe pt -> do
            let t = desugarT pt
            e <- go pe
            return $ e ::: t
          --e -> error $ "Compiler error: missing case in desugarE: " ++ show e
        po1 primop a = Var primop :$ a
        po2 primop a b =
          Var primop :$ (Var "Pair" :$ a :$
                          (Var "Pair" :$ b :$ Var "Unit"))
        op1 :: Name -> P.E -> De E
        op1 primop a = po1 primop <$> go a
        op2 primop a b = po2 primop <$> go a <*> go b
        aop2op = \case
          P.EqEq -> flip const
          P.PlusEq -> po2 "plus"
          P.MinusEq -> po2 "minus"
          P.MulEq -> po2 "multiply"
          P.DivEq -> po2 "divide"
          P.ModEq -> po2 "modulo"
          P.ShlEq -> po2 "shL"
          P.ShrEq -> po2 "shR"
          P.AndEq -> po2 "bwAnd"
          P.XorEq -> po2 "bwXor"
          P.OrEq -> po2 "bwOr"
-}
    {-
    go = \case
      P.String str -> do
        let len = length str
        handleStaticDataExpr (Array (UInt 8) $ fromIntegral len) $
          structE $ map (EInteger . fromIntegral . ord) str
      --TODO distinguish name types in the AST type?
      --The only valid use of standalone uppercase names is enum values
      P.Con (UIdent nm) -> return $ Var nm
      P.Wild -> throwE WildcardInExprContext
      P.BlockE pss -> BlockE <$> mapM desugarS pss
      P.PlusPlusPost pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        temp <- newDeName "temp"
        return $ BlockE [
          SE $ PVar temp := expr,
          SE $ pat := PrimOp "+" [Var temp,EInteger 1],
          LocalReturn 0 $ Var temp
          ]
      P.MinusMinusPost pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        temp <- newDeName "temp"
        return $ BlockE [
          SE $ PVar temp := expr,
          SE $ pat := PrimOp "-" [Var temp,EInteger 1],
          LocalReturn 0 $ Var temp
          ]
      P.Index arr ix -> po "index" [arr,ix]
      --Fold field accesses into a single Dots
      --That's better done in a later traversal...
      --Note that ideally x = a.b; y = x.c would be caught via symbolic eval
      P.Dot pe (Ident nm) -> do
        e <- go pe
        return $ Dots e [Left nm]
      P.Arrow pe field -> go $ P.Deref pe `P.Dot` field
      --Can now no longer be confused with primfun applications, modulo
      --prefix ident primfuns
      P.App (P.Var (Ident nm)) pe
        | S.member nm prefixPrimfuns -> do
            es <- desugarExplicitTuple pe
            return $ PrimOp nm es
      --However, Con arg also uses P.App:
      P.App (P.Con (UIdent con)) parg -> do
        arg <- go parg
        return $ Con con arg
      P.App f x -> (:$) <$> go f <*> go x
      -- ++x =>
      --block {
      -- x += 1;
      -- localReturn 0 x
      -- }
      --Todo deduplicate
      P.PlusPlusPre pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        return $ BlockE [
          SE $ pat := PrimOp "+" [expr,EInteger 1],
          LocalReturn 0 expr
          ]
      P.MinusMinusPre pe -> do
        pat <- incLRDepthP 0 <$> desugarP pe
        expr <- incLRDepth 0 <$> go pe
        return $ BlockE [
          SE $ pat := PrimOp "-" [expr,EInteger 1],
          LocalReturn 0 expr
          ]
      --Unary - now has its own primfun
      P.Negate pe -> po "negate" [pe]
      P.Not pe -> po "!" [pe]
      P.BitwiseNot pe -> po "~" [pe]
      --Add a pattern synonym for Deref in E?
      P.Deref pe -> po "deref" [pe]
      --It's not strictly a primop...
      P.AddressOf pe -> po "&_" [pe]
      --We split the alloc ptr into pat and expr here to avoid needing to do
      --so in later stages.
      P.At a b -> do
        a' <- desugarE a
        bp <- desugarP b
        be <- desugarE b
        return $ a' :@ (bp,be)
      P.Mul a b -> po "*" [a,b]
      P.Div a b -> po "/" [a,b]
      P.Mod a b -> po "%" [a,b]
      P.Plus a b -> po "+" [a,b]
      P.Minus a b -> po "-" [a,b]
      P.Shl a b -> po "<<" [a,b]
      P.Shr a b -> po ">>" [a,b]
      --Note only <, <=, ==, != primops are supported
      P.MyLT a b -> po "<" [a,b]
      P.LTE a b -> po "<=" [a,b]
      P.MyGT a b -> po "<" [b,a]
      P.GTE a b -> po "<=" [b,a]
      P.Eq a b -> po "==" [a,b]
      P.NEq a b -> po "!=" [a,b]
      P.BitwiseAnd a b -> po "&" [a,b]
      P.BitwiseXor a b -> po "^" [a,b]
      P.BitwiseOr  a b -> po "|" [a,b]
      --Desugar to block expressions
      --a && b =>
      --block {
      -- if a
      -- then localReturn 0 truthy b
      -- else localReturn 0 0
      -- }
      --Note a and b may contain explicit local returns, so their return
      --index needs to be incremented.
      P.And a b -> do
        a' <- incLRDepth 0 <$> go a
        b' <- incLRDepth 0 <$> go b
        return $ BlockE [
          Ifte a' (LocalReturn 0 $ PrimOp "truthy" [b'])
            (LocalReturn 0 $ EInteger 0)
          ]
      P.Or a b -> do
        a' <- incLRDepth 0 <$> go a
        b' <- incLRDepth 0 <$> go b
        return $ BlockE [
          Ifte a' (LocalReturn 0 $ EInteger 1)
            (LocalReturn 0 $ PrimOp "truthy" [b'])
          ]
      --Desugar += etc to block expressions
      --TODO opt: *p.a.b.c += e to avoid duplicating the address calc
      --a.b.c |= or ^= could also be easily optimized
      -- +=, *= are less straightforward due to overflow
      P.Assign lhs aop rhs -> do
        p <- desugarP lhs
        e <- desugarE rhs
        case aop of
          P.EqEq ->
            return $ p := e
          _ -> do
            let primop = case aop of
                           P.PlusEq -> "+"
                           P.MinusEq -> "-"
                           P.MulEq -> "*"
                           P.DivEq -> "/"
                           P.ModEq -> "%"
                           P.ShlEq -> "<<"
                           P.ShrEq -> ">>"
                           P.AndEq -> "&"
                           P.XorEq -> "^"
                           P.OrEq -> "|"
            --Note string allocation is duplicated here; opt to get rid of it
            oldp <- desugarE lhs
            return $ p := PrimOp primop [oldp,e]
      P.Coerce e t -> Coerce (desugarT t) <$> go e
      P.TypeIs e t -> TypeIs (desugarT t) <$> go e
      P.UnsafeCoerce e t -> UnsafeCoerce (desugarT t) <$> go e
    po nm es = PrimOp nm <$> mapM go es
-}

--"abc" => (&sv :: Ptr Code (Array 3 Byte)) where sv := array (97,98,99)
handleString :: String -> De E
handleString str = error "todo"
  {-
  do
  let codes = map ord str
      len = fromIntegral $ length str
  --Better than silently truncating...
  complainIf (any (>255) codes)
    $ NonByteChar str
  --sv := array cs
  let arrayE = EArray $ map (EInteger . fromIntegral) codes
  s <- get
  --Alloc new name for sv, insert new sv def
  let n = anonStaticCtr s
      svnm = "$static" ++ show n
  put s{anonStaticCtr = n + 1,
        static = M.insert svnm arrayE $ static s}
  return $ (Var "ampersand" :$ Var svnm)
    ::: Ptr Code (Array (TyNat len) (TyCon "Byte"))
-}

--String literals are lifted to staticData decls:
--"abc" becomes staticData (Byte[3]) {97,98,99};
--staticData t e expressions are desugared further to
--newname : Ptr Code t with an accompanying
--staticData t newname = e
--declaration.
{-
Permitted static exprs:
k (integer constants),
-k (negation can be applied statically),
var: function, constructor, staticdata name
&global, &staticdata
tuple --desugars to con apps
Con arg

In theory arbitrary expressions could be permitted, but something like
&global + k would require a more expressive linker - better to keep the
limitations explicit and leave it to the programmer to implement their own
custom creation script logic when necessary.
-}
