-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Builder (
  emit, emitHinted, emitOp, emitUnOp,
  buildPureLam, BuilderT (..), Builder (..), ScopableBuilder (..),
  buildScopedAssumeNoDecls,
  Builder2, BuilderM, ScopableBuilder2,
  liftBuilderT, buildBlock, withType, absToBlock, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, buildPureNaryLam, emitMethod,
  select, getUnpacked, emitUnpacked, unwrapBaseNewtype, unwrapCompoundNewtype,
  fromPair, getFst, getSnd, getProj, getProjRef, getNaryProjRef,
  naryApp, naryAppHinted,
  tabApp, naryTabApp, naryTabAppHinted,
  indexRef, naryIndexRef,
  ptrOffset, unsafePtrLoad,
  getClassDef, getDataCon,
  Emits, EmitsEvidence (..), buildPi, buildNonDepPi,
  buildLam, buildTabLam, buildLamGeneral,
  buildAbs, buildNaryAbs, buildNaryLam, buildNullaryLam, buildNaryLamExpr, asNaryLam,
  buildAlt, buildUnaryAtomAlt,
  emitDataDef, emitClassDef, emitInstanceDef, emitDataConName, emitTyConName,
  emitEffectDef, emitHandlerDef, emitEffectOpDef,
  buildCase, emitMaybeCase, buildSplitCase,
  emitBlock, emitDecls, BuilderEmissions, emitExprToAtom, emitAtomToName,
  TopBuilder (..), TopBuilderT (..), liftTopBuilderTWith,
  runTopBuilderT, TopBuilder2, emitBindingDefault,
  emitSourceMap, emitSynthCandidates, addInstanceSynthCandidate,
  emitTopLet, emitImpFunBinding, emitSpecialization, emitAtomRules,
  lookupLoadedModule, bindModule, extendCache, lookupLoadedObject, extendLoadedObjects,
  extendImpCache, queryImpCache, finishSpecializedDict,
  extendSpecializationCache, querySpecializationCache, getCache, emitObjFile, lookupPtrName,
  queryIxDictCache, extendIxDictCache,
  extendObjCache, queryObjCache,
  TopEnvFrag (..), emitPartialTopEnvFrag, emitLocalModuleEnv, emitLoweredFun,
  fabricateEmitsEvidence, fabricateEmitsEvidenceM,
  singletonBinderNest, varsAsBinderNest, typesAsBinderNest,
  liftBuilder, liftEmitBuilder, makeBlock, absToBlockInferringTypes,
  ordinal, indexSetSize, unsafeFromOrdinal, projectIxFinMethod,
  telescopicCapture, unpackTelescope,
  applyRecon, applyReconAbs, applyIxMethod,
  emitRunWriter, emitRunState, emitRunReader, buildFor, unzipTab, buildForAnn,
  zeroAt, zeroLike, maybeTangentType, tangentType,
  addTangent, updateAddAt, tangentBaseMonoidFor,
  buildEffLam, catMaybesE, runMaybeWhile,
  ReconAbs, ReconstructAtom (..), buildNullaryPi, buildNaryPi,
  HoistingTopBuilder (..), liftTopBuilderHoisted,
  DoubleBuilderT (..), DoubleBuilder, liftDoubleBuilderT,
  liftDoubleBuilderTNoEmissions, runDoubleBuilderT, toposortAnnVars
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State.Strict (MonadState, StateT (..), runStateT)
import qualified Data.Map.Strict as M
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Graph (graphFromEdges, topSort)
import Data.Text.Prettyprint.Doc (Pretty (..), group, line, nest)
import GHC.Stack

import qualified Unsafe.Coerce as TrulyUnsafe

import qualified RawName as R
import Name
import Syntax
import QueryType
import PPrint (prettyBlock)
import CheapReduction
import MTL1
import {-# SOURCE #-} Interpreter
import LabeledItems
import Util (enumerate, transitiveClosureM, bindM2, toSnocList)
import Err
import Types.Core
import Core

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m)
      => Builder (r::IR) (m::MonadKind1) | m -> r where
  emitDecl :: Emits n => NameHint -> LetAnn -> Expr r n -> m n (AtomName r n)

class Builder r m => ScopableBuilder (r::IR) (m::MonadKind1) | m -> r where
  buildScoped
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (Abs (Nest (Decl r)) e n)

type Builder2         (r::IR) (m :: MonadKind2) = forall i. Builder         r (m i)
type ScopableBuilder2 (r::IR) (m :: MonadKind2) = forall i. ScopableBuilder r (m i)

emit :: (Builder r m, Emits n) => Expr r n -> m n (AtomName r n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitHinted :: (Builder r m, Emits n) => NameHint -> Expr r n -> m n (AtomName r n)
emitHinted hint expr = emitDecl hint PlainLet expr
{-# INLINE emitHinted #-}

emitOp :: (Builder r m, Emits n) => Op r n -> m n (Atom r n)
emitOp op = Var <$> emit (Op op)
{-# INLINE emitOp #-}

emitUnOp :: (Builder r m, Emits n) => UnOp -> Atom r n -> m n (Atom r n)
emitUnOp op x = emitOp $ UnOp op x
{-# INLINE emitUnOp #-}

emitBlock :: (Builder r m, Emits n) => Block r n -> m n (Atom r n)
emitBlock (Block _ decls result) = emitDecls decls result

emitDecls :: (Builder r m, Emits n, SubstE Name e, SinkableE e)
          => Nest (Decl r) n l -> e l -> m n (e n)
emitDecls decls result = runSubstReaderT idSubst $ emitDecls' decls result

emitDecls' :: (Builder r m, Emits o, SubstE Name e, SinkableE e)
           => Nest (Decl r) i i' -> e i' -> SubstReaderT Name m i o (e o)
emitDecls' Empty e = substM e
emitDecls' (Nest (Let b (DeclBinding ann _ expr)) rest) e = do
  expr' <- substM expr
  v <- emitDecl (getNameHint b) ann expr'
  extendSubst (b @> v) $ emitDecls' rest e

emitExprToAtom :: (Builder r m, Emits n) => Expr r n -> m n (Atom r n)
emitExprToAtom (Atom atom) = return atom
emitExprToAtom expr = Var <$> emit expr
{-# INLINE emitExprToAtom #-}

emitAtomToName :: (Builder r m, Emits n) => NameHint -> Atom r n -> m n (AtomName r n)
emitAtomToName _ (Var v) = return v
emitAtomToName hint x = emitHinted hint (Atom x)
{-# INLINE emitAtomToName #-}

buildScopedAssumeNoDecls :: (SinkableE e, ScopableBuilder r m)
  => (forall l. (Emits l, DExt n l) => m l (e l))
  -> m n (e n)
buildScopedAssumeNoDecls cont = do
  buildScoped cont >>= \case
    (Abs Empty e) -> return e
    _ -> error "Expected no decl emissions"
{-# INLINE buildScopedAssumeNoDecls #-}

-- === "Hoisting" top-level builder class ===

-- `emitHoistedEnv` lets you emit top env fragments, like cache entries or
-- top-level function definitions, from within a local context. The operation
-- may fail, returning `Nothing`, because the emission might mention local
-- variables that can't be hoisted the top level.
class (EnvReader m, MonadFail1 m) => HoistingTopBuilder frag m | m -> frag where
  emitHoistedEnv :: (SinkableE e, SubstE Name e, HoistableE e)
                 => Abs frag e n -> m n (Maybe (e n))
  canHoistToTop :: HoistableE e => e n -> m n Bool

liftTopBuilderHoisted
  :: (EnvReader m, SubstE Name e, SinkableE e, HoistableE e)
  => (forall l. (Mut l, DExt n l) => TopBuilderM l (e l))
  -> m n (Abs TopEnvFrag e n)
liftTopBuilderHoisted cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runHardFail $ runTopBuilderT env $ localTopBuilder cont

newtype DoubleBuilderT (r::IR) (topEmissions::B) (m::MonadKind) (n::S) (a:: *) =
  DoubleBuilderT { runDoubleBuilderT' :: DoubleInplaceT Env topEmissions (BuilderEmissions r) m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, MonadIO, Catchable, MonadReader r')

deriving instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m)
                  => ScopeReader (DoubleBuilderT r frag m)

type DoubleBuilder r = DoubleBuilderT r TopEnvFrag HardFailM

liftDoubleBuilderTNoEmissions
  :: (EnvReader m, Fallible m') => DoubleBuilderT r UnitB m' n a -> m n (m' a)
liftDoubleBuilderTNoEmissions cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    Abs UnitB (DoubleInplaceTResult REmpty (LiftE ans)) <-
      -- XXX: it's safe to use `unsafeCoerceM1` here. We don't need the rank-2
      -- trick because we've specialized on the `UnitB` case, so there can't be
      -- any top emissions.
      runDoubleInplaceT env $ unsafeCoerceM1 $ runDoubleBuilderT' $ LiftE <$> cont
    return ans

-- TODO: do we really need to play these rank-2 games here?
liftDoubleBuilderT
  :: ( EnvReader m, Fallible m', SinkableE e, SubstE Name e
     , ExtOutMap Env frag, OutFrag frag)
  => (forall l. DExt n l => DoubleBuilderT r frag m' l (e l))
  -> m n (m' (Abs frag e n))
liftDoubleBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runDoubleBuilderT env cont

runDoubleBuilderT
  :: ( Distinct n, Fallible m, SinkableE e, SubstE Name e
     , ExtOutMap Env frag, OutFrag frag)
  => Env n
  -> (forall l. DExt n l => DoubleBuilderT r frag m l (e l))
  -> m (Abs frag e n)
runDoubleBuilderT env cont = do
  Abs envFrag (DoubleInplaceTResult REmpty e) <-
    runDoubleInplaceT env $ runDoubleBuilderT' cont
  return $ Abs envFrag e

instance (ExtOutMap Env f, OutFrag f, SubstB Name f, HoistableB f, Fallible m)
  => HoistingTopBuilder f (DoubleBuilderT r f m) where
  emitHoistedEnv ab = DoubleBuilderT $ emitDoubleInplaceTHoisted ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = DoubleBuilderT $ canHoistToTopDoubleInplaceT e
  {-# INLINE canHoistToTop #-}

instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m) => EnvReader (DoubleBuilderT r frag m) where
  unsafeGetEnv = DoubleBuilderT $ liftDoubleInplaceT $ unsafeGetEnv

instance ( SubstB Name frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
        => Builder r (DoubleBuilderT r frag m) where
  emitDecl hint ann e = DoubleBuilderT $ liftDoubleInplaceT $ runBuilderT' $ emitDecl hint ann e

instance ( SubstB Name frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
         => ScopableBuilder r (DoubleBuilderT r frag m) where
  -- TODO: find a safe API for DoubleInplaceT sufficient to implement this
  buildScoped cont = DoubleBuilderT do
    (ans, decls) <- UnsafeMakeDoubleInplaceT $
      StateT \s@(topScope, _) -> do
        Abs rdecls (PairE e (LiftE topDecls)) <-
          locallyMutableInplaceT do
            (e, (_, topDecls)) <- flip runStateT (topScope, emptyOutFrag) $
               unsafeRunDoubleInplaceT $ runDoubleBuilderT' do
                 Emits <- fabricateEmitsEvidenceM
                 Distinct <- getDistinct
                 cont
            return $ PairE e $ LiftE topDecls
        return ((Abs (unRNest rdecls) e, topDecls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
  {-# INLINE buildScoped #-}

-- TODO: derive this instead
instance ( SubstB Name frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
         => EnvExtender (DoubleBuilderT r frag m) where
  refreshAbs ab cont = DoubleBuilderT do
    (ans, decls) <- UnsafeMakeDoubleInplaceT do
      StateT \s@(topScope, _) -> do
        (ans, (_, decls)) <- refreshAbs ab \b e -> do
          flip runStateT (topScope, emptyOutFrag) $
            unsafeRunDoubleInplaceT $ runDoubleBuilderT' $ cont b e
        return ((ans, decls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
  {-# INLINE refreshAbs #-}

instance (SinkableV v, HoistingTopBuilder f m) => HoistingTopBuilder f (SubstReaderT v m i) where
  emitHoistedEnv ab = SubstReaderT $ lift $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = SubstReaderT $ lift $ canHoistToTop e
  {-# INLINE canHoistToTop #-}

-- === Top-level builder class ===

class (EnvReader m, MonadFail1 m)
      => TopBuilder (m::MonadKind1) where
  -- `emitBinding` is expressible in terms of `emitEnv` but it can be
  -- implemented more efficiently by avoiding a double substitution
  -- XXX: emitBinding/emitEnv don't extend the synthesis candidates
  -- TODO: do we actually need `emitBinding`? Top emissions probably aren't hot.
  emitBinding :: Mut n => Color c => NameHint -> Binding c n -> m n (Name c n)
  emitEnv :: (Mut n, SinkableE e, SubstE Name e) => Abs TopEnvFrag e n -> m n (e n)
  emitNamelessEnv :: TopEnvFrag n n -> m n ()
  localTopBuilder :: SinkableE e
                  => (forall l. (Mut l, DExt n l) => m l (e l))
                  -> m n (Abs TopEnvFrag e n)

emitBindingDefault
  :: (TopBuilder m, Mut n, Color c)
  => NameHint -> Binding c n -> m n (Name c n)
emitBindingDefault hint binding = do
  ab <- liftEnvReaderM $ withFreshBinder hint binding \b'-> do
    let topFrag = TopEnvFrag (toEnvFrag (b':>binding)) mempty
    return $ Abs topFrag $ binderName b'
  emitEnv ab

emitPartialTopEnvFrag :: TopBuilder m => PartialTopEnvFrag n -> m n ()
emitPartialTopEnvFrag frag = emitNamelessEnv $ TopEnvFrag emptyOutFrag frag

emitLocalModuleEnv :: TopBuilder m => ModuleEnv n -> m n ()
emitLocalModuleEnv env = emitPartialTopEnvFrag $ mempty { fragLocalModuleEnv = env }

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitLocalModuleEnv $ mempty {envSourceMap = sm}

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitLocalModuleEnv $ mempty {envSynthCandidates = sc}

addInstanceSynthCandidate :: TopBuilder m => ClassName n -> InstanceName n -> m n ()
addInstanceSynthCandidate className instanceName =
  emitSynthCandidates $ SynthCandidates [] (M.singleton className [instanceName])

emitAtomRules :: TopBuilder m => AtomName r n -> AtomRules n -> m n ()
emitAtomRules v rules = emitNamelessEnv $
  TopEnvFrag emptyOutFrag $ mempty { fragCustomRules = CustomRules $ M.singleton v rules }

emitTopLet :: (Mut n, TopBuilder m) => NameHint -> LetAnn -> Expr r n -> m n (AtomName r n)
emitTopLet hint letAnn expr = do
  ty <- getType expr
  emitBinding hint $ AtomNameBinding $ unsafeCoerceIRE $ LetBound (DeclBinding letAnn ty expr)

emitImpFunBinding :: (Mut n, TopBuilder m) => NameHint -> ImpFunction n -> m n (ImpFunName n)
emitImpFunBinding hint f = emitBinding hint $ ImpFunBinding f

emitSpecialization
  :: (Mut n, TopBuilder m)
  => SpecializationSpec n -> m n (AtomName r n)
emitSpecialization s = do
  let hint = getNameHint s
  specializedTy <- specializedFunType s
  let binding = TopFunBound specializedTy $ SpecializedTopFun s
  name <- emitBinding hint $ toBinding binding
  extendSpecializationCache s name
  return name

bindModule :: (Mut n, TopBuilder m) => ModuleSourceName -> ModuleName n -> m n ()
bindModule sourceName internalName = do
  let loaded = LoadedModules $ M.singleton sourceName internalName
  emitPartialTopEnvFrag $ mempty {fragLoadedModules = loaded}

lookupLoadedModule:: EnvReader m => ModuleSourceName -> m n (Maybe (ModuleName n))
lookupLoadedModule name = do
  loadedModules <- withEnv $ envLoadedModules . topEnv
  return $ M.lookup name $ fromLoadedModules loadedModules

lookupLoadedObject :: EnvReader m => FunObjCodeName n -> m n (Maybe NativeFunction)
lookupLoadedObject name = do
  loadedObjects <- withEnv $ envLoadedObjects . topEnv
  return $ M.lookup name $ fromLoadedObjects loadedObjects

extendLoadedObjects :: (Mut n, TopBuilder m) => FunObjCodeName n -> NativeFunction -> m n ()
extendLoadedObjects name ptr = do
  let loaded = LoadedObjects $ M.singleton name ptr
  emitPartialTopEnvFrag $ mempty {fragLoadedObjects = loaded}

extendCache :: TopBuilder m => Cache n -> m n ()
extendCache cache = emitPartialTopEnvFrag $ mempty {fragCache = cache}

extendImpCache :: TopBuilder m => AtomName r n -> ImpFunName n -> m n ()
extendImpCache fSimp fImp =
  extendCache $ mempty { impCache = eMapSingleton fSimp fImp }

queryImpCache :: EnvReader m => AtomName r n -> m n (Maybe (ImpFunName n))
queryImpCache v = do
  cache <- impCache <$> getCache
  return $ lookupEMap cache v

emitLoweredFun :: (Mut n, TopBuilder m) => NameHint -> NaryLamExpr SimpIR n -> m n (AtomName r n)
emitLoweredFun hint f = do
  fTy <- naryLamExprType f
  emitBinding hint $ AtomNameBinding $ TopFunBound fTy (LoweredTopFun f)

extendSpecializationCache :: TopBuilder m => SpecializationSpec n -> AtomName r n -> m n ()
extendSpecializationCache specialization f =
  extendCache $ mempty { specializationCache = eMapSingleton specialization f }

querySpecializationCache :: EnvReader m => SpecializationSpec n -> m n (Maybe (AtomName r n))
querySpecializationCache specialization = do
  cache <- specializationCache <$> getCache
  return $ lookupEMap cache specialization

extendIxDictCache :: TopBuilder m => AbsDict r n -> Name SpecializedDictNameC n -> m n ()
extendIxDictCache absDict name =
  extendCache $ mempty { ixDictCache = eMapSingleton (unsafeCoerceRAbsDict absDict) name }

queryIxDictCache :: EnvReader m => AbsDict r n -> m n (Maybe (Name SpecializedDictNameC n))
queryIxDictCache d = do
  cache <- ixDictCache <$> getCache
  return $ lookupEMap cache (unsafeCoerceRAbsDict d)

unsafeCoerceRAbsDict :: AbsDict r n -> AbsDict r' n
unsafeCoerceRAbsDict (Abs bs e) = Abs bs' (unsafeCoerceIRE e)
  where bs' = fmapNest (\(b:>ty) -> b :> unsafeCoerceIRE ty) bs

finishSpecializedDict :: (Mut n, TopBuilder m) => SpecDictName n -> [NaryLamExpr SimpIR n] -> m n ()
finishSpecializedDict name methods =
  emitPartialTopEnvFrag $ mempty {fragFinishSpecializedDict = toSnocList [(name, methods)]}

extendObjCache :: (Mut n, TopBuilder m) => ImpFunName n -> FunObjCodeName n -> m n ()
extendObjCache fImp fObj =
  extendCache $ mempty { objCache = eMapSingleton fImp fObj }

queryObjCache :: EnvReader m => ImpFunName n -> m n (Maybe (FunObjCodeName n))
queryObjCache v = do
  cache <- objCache <$> getCache
  return $ lookupEMap cache v

emitObjFile
  :: (Mut n, TopBuilder m)
  => NameHint -> FunObjCode -> LinktimeNames  n
  -> m n (FunObjCodeName n)
emitObjFile hint objFile names = do
  emitBinding hint $ FunObjCodeBinding objFile names

lookupPtrName :: EnvReader m => PtrName n -> m n (PtrType, Ptr ())
lookupPtrName v = lookupEnv v >>= \case
  PtrBinding ty p -> case p of
    PtrLitVal ptr -> return (ty, ptr)
    PtrSnapshot _ -> error "this case is only for serialization"
    NullPtr       -> error "not implemented"

getCache :: EnvReader m => m n (Cache n)
getCache = withEnv $ envCache . topEnv

newtype TopBuilderT (m::MonadKind) (n::S) (a:: *) =
  TopBuilderT { runTopBuilderT' :: InplaceT Env TopEnvFrag m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader, MonadTrans1, MonadReader r
           , MonadWriter w, MonadState s, MonadIO, Catchable)

type TopBuilderM = TopBuilderT HardFailM

-- We use this to implement things that look like `local` from `MonadReader`.
-- Does it make sense to but it in a transformer-like class, like we do with
-- `lift11`?
liftTopBuilderTWith :: Monad m => (forall a'. m a' -> m a')
                    -> TopBuilderT m n a -> TopBuilderT m n a
liftTopBuilderTWith modifyInner cont = TopBuilderT $
  liftBetweenInplaceTs modifyInner id id (runTopBuilderT' cont)

instance Fallible m => EnvReader (TopBuilderT m) where
  unsafeGetEnv = TopBuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance Fallible m => TopBuilder (TopBuilderT m) where
  emitBinding hint binding = do
    Abs b v <- freshNameM hint
    let ab = Abs (b:>binding) v
    ab' <- liftEnvReaderM $ refreshAbs ab \b' v' -> do
      let envFrag = toEnvFrag b'
      let scs = bindingsFragToSynthCandidates envFrag
      let topFrag = TopEnvFrag envFrag $
            mempty { fragLocalModuleEnv = mempty { envSynthCandidates = scs} }
      return $ Abs topFrag v'
    TopBuilderT $ extendInplaceT ab'

  emitEnv ab = TopBuilderT $ extendInplaceT ab
  {-# INLINE emitEnv #-}

  emitNamelessEnv bs = TopBuilderT $ extendTrivialInplaceT bs
  {-# INLINE emitNamelessEnv #-}

  localTopBuilder cont = TopBuilderT $
    locallyMutableInplaceT $ runTopBuilderT' cont
  {-# INLINE localTopBuilder #-}

instance (SinkableV v, TopBuilder m) => TopBuilder (SubstReaderT v m i) where
  emitBinding hint binding = SubstReaderT $ lift $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = SubstReaderT $ lift $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv bs = SubstReaderT $ lift $ emitNamelessEnv bs
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder cont = SubstReaderT $ ReaderT \env -> do
    localTopBuilder do
      Distinct <- getDistinct
      runReaderT (runSubstReaderT' cont) (sink env)
  {-# INLINE localTopBuilder #-}

runTopBuilderT
  :: (Fallible m, Distinct n)
  => Env n
  -> TopBuilderT m n a
  -> m a
runTopBuilderT bindings cont = do
  liftM snd $ runInplaceT bindings $ runTopBuilderT' $ cont
{-# INLINE runTopBuilderT #-}

type TopBuilder2 (r::IR) (m :: MonadKind2) = forall i. TopBuilder (m i)

instance (SinkableE e, HoistableState e, TopBuilder m) => TopBuilder (StateT1 e m) where
  emitBinding hint binding = lift11 $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = lift11 $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv frag = lift11 $ emitNamelessEnv frag
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder _ = error "not implemented"

-- === BuilderT ===

type BuilderEmissions r = RNest (Decl r)

newtype BuilderT (r::IR) (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT Env (BuilderEmissions r) m n a }
  deriving ( Functor, Applicative, Monad, MonadTrans1, MonadFail, Fallible
           , CtxReader, ScopeReader, Alternative, Searcher
           , MonadWriter w, MonadReader r')

type BuilderM (r::IR) = BuilderT r HardFailM

liftBuilderT :: (Fallible m, EnvReader m') => BuilderT r m n a -> m' n (m a)
liftBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    (REmpty, result) <- runInplaceT env $ runBuilderT' cont
    return result
{-# INLINE liftBuilderT #-}

liftBuilder :: EnvReader m => BuilderM r n a -> m n a
liftBuilder cont = liftM runHardFail $ liftBuilderT cont
{-# INLINE liftBuilder #-}

-- TODO: This should not fabricate Emits evidence!!
-- XXX: this uses unsafe functions in its implementations. It should be safe to
-- use, but be careful changing it.
liftEmitBuilder :: (Builder r m, SinkableE e, SubstE Name e)
                => BuilderM r n (e n) -> m n (e n)
liftEmitBuilder cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let (result, decls, _) = runHardFail $ unsafeRunInplaceT (runBuilderT' cont) env emptyOutFrag
  Emits <- fabricateEmitsEvidenceM
  emitDecls (unsafeCoerceB $ unRNest decls) result

instance Fallible m => ScopableBuilder r (BuilderT r m) where
  buildScoped cont = BuilderT do
    Abs rdecls e <- locallyMutableInplaceT $
      runBuilderT' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont
    return $ Abs (unRNest rdecls) e
  {-# INLINE buildScoped #-}

newtype BuilderDeclEmission (r::IR) (n::S) (l::S) = BuilderDeclEmission (Decl r n l)
instance ExtOutMap Env (BuilderDeclEmission r) where
  extendOutMap env (BuilderDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag (BuilderEmissions r) (BuilderDeclEmission r) where
  extendOutFrag rn (BuilderDeclEmission d) = RNest rn d
  {-# INLINE extendOutFrag #-}

instance Fallible m => Builder r (BuilderT r m) where
  emitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $ freshExtendSubInplaceT hint \b ->
      (BuilderDeclEmission $ Let b $ DeclBinding ann ty expr, binderName b)
  {-# INLINE emitDecl #-}

instance Fallible m => EnvReader (BuilderT r m) where
  unsafeGetEnv = BuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance Fallible m => EnvExtender (BuilderT r m) where
  refreshAbs ab cont = BuilderT $ refreshAbs ab \b e -> runBuilderT' $ cont b e
  {-# INLINE refreshAbs #-}

instance (SinkableV v, ScopableBuilder r m) => ScopableBuilder r (SubstReaderT v m i) where
  buildScoped cont = SubstReaderT $ ReaderT \env ->
    buildScoped $
      runReaderT (runSubstReaderT' cont) (sink env)
  {-# INLINE buildScoped #-}

instance (SinkableV v, Builder r m) => Builder r (SubstReaderT v m i) where
  emitDecl hint ann expr = SubstReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (OutReaderT e m) where
  buildScoped cont = OutReaderT $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runOutReaderT' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder r m) => Builder r (OutReaderT e m) where
  emitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (ReaderT1 e m) where
  buildScoped cont = ReaderT1 $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runReaderT1' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder r m) => Builder r (ReaderT1 e m) where
  emitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, HoistableState e, Builder r m) => Builder r (StateT1 e m) where
  emitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, HoistableState e, ScopableBuilder r m) => ScopableBuilder r (StateT1 e m) where
  buildScoped cont = StateT1 \s -> do
    Abs decls (e `PairE` s') <- buildScoped $ liftM toPairE $ runStateT1 cont =<< sinkM s
    let s'' = hoistState s decls s'
    return (Abs decls e, s'')
  {-# INLINE buildScoped #-}

instance (SinkableE e, HoistableState e, HoistingTopBuilder frag m)
  => HoistingTopBuilder frag (StateT1 e m) where
  emitHoistedEnv ab = lift11 $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = lift11 $ canHoistToTop e
  {-# INLINE canHoistToTop #-}

instance Builder r m => Builder r (MaybeT1 m) where
  emitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

class Mut n => Emits (n::S)
data EmitsEvidence (n::S) where
  Emits :: Emits n => EmitsEvidence n
instance Emits UnsafeS

fabricateEmitsEvidence :: forall n. EmitsEvidence n
fabricateEmitsEvidence = withFabricatedEmits @n Emits
{-# INLINE fabricateEmitsEvidence #-}

fabricateEmitsEvidenceM :: forall m n. Monad1 m => m n (EmitsEvidence n)
fabricateEmitsEvidenceM = return fabricateEmitsEvidence
{-# INLINE fabricateEmitsEvidenceM #-}

withFabricatedEmits :: forall n a. (Emits n => a) -> a
withFabricatedEmits cont = fromWrapWithEmits
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmits cont :: WrapWithEmits n       a
                                               ) :: WrapWithEmits UnsafeS a)
{-# INLINE withFabricatedEmits #-}

newtype WrapWithEmits n r =
  WrapWithEmits { fromWrapWithEmits :: Emits n => r }

-- === lambda-like things ===

buildBlock
  :: ScopableBuilder r m
  => (forall l. (Emits l, DExt n l) => m l (Atom r l))
  -> m n (Block r n)
buildBlock cont = buildScoped (cont >>= withType) >>= computeAbsEffects >>= absToBlock

withType :: (EnvReader m, HasType r e) => e l -> m l ((e `PairE` Type r) l)
withType e = do
  ty <- {-# SCC blockTypeNormalization #-} cheapNormalize =<< getType e
  return $ e `PairE` ty
{-# INLINE withType #-}

makeBlock :: Nest (Decl r) n l -> EffectRow l -> Atom r l -> Type r l -> Block r n
makeBlock decls effs atom ty = Block (BlockAnn ty' effs') decls atom where
  ty' = ignoreHoistFailure $ hoist decls ty
  effs' = ignoreHoistFailure $ hoist decls effs
{-# INLINE makeBlock #-}

absToBlockInferringTypes :: EnvReader m => Abs (Nest (Decl r)) (Atom r) n -> m n (Block r n)
absToBlockInferringTypes ab = liftEnvReaderM do
  abWithEffs <-  computeAbsEffects ab
  refreshAbs abWithEffs \decls (effs `PairE` result) -> do
    ty <- cheapNormalize =<< getType result
    return $ ignoreExcept $
      absToBlock $ Abs decls (effs `PairE` (result `PairE` ty))
{-# INLINE absToBlockInferringTypes #-}

absToBlock :: (Fallible m) => Abs (Nest (Decl r)) (EffectRow `PairE` (Atom r `PairE` Type r)) n -> m (Block r n)
absToBlock (Abs decls (effs `PairE` (result `PairE` ty))) = do
  let msg = "Block:" <> nest 1 (prettyBlock decls result) <> line
            <> group ("Of type:" <> nest 2 (line <> pretty ty)) <> line
            <> group ("With effects:" <> nest 2 (line <> pretty effs))
  ty' <- liftHoistExcept' (docAsStr msg) $ hoist decls ty
  effs' <- liftHoistExcept' (docAsStr msg) $ hoist decls effs
  return $ Block (BlockAnn ty' effs') decls result
{-# INLINE absToBlock #-}

buildPureLam :: ScopableBuilder r m
             => NameHint -> Arrow -> Type r n
             -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
             -> m n (Atom r n)
buildPureLam hint arr ty body = do
  buildLamGeneral hint arr ty (const $ return Pure) \v -> do
    Distinct <- getDistinct
    body v

buildTabLam
  :: ScopableBuilder r m
  => NameHint -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildTabLam hint ty fBody = do
  withFreshBinder hint ty \b -> do
    let v = binderName b
    body <- withAllowedEffects Pure $ buildBlock $ fBody $ sink v
    return $ TabLam $ TabLamExpr (b:>ty) body

buildLam
  :: ScopableBuilder r m
  => NameHint -> Arrow -> Type r n -> EffectRow n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildLam hint arr ty eff body = buildLamGeneral hint arr ty (const $ sinkM eff) body

buildNullaryLam :: ScopableBuilder r m
                => EffectRow n
                -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
                -> m n (Atom r n)
buildNullaryLam effs cont = buildLam noHint PlainArrow UnitTy effs \_ -> cont

buildNullaryPi :: Builder r m
               => EffectRow n
               -> (forall l. DExt n l => m l (Type r l))
               -> m n (Type r n)
buildNullaryPi effs cont =
  Pi <$> buildPi noHint PlainArrow UnitTy \_ -> do
    resultTy <- cont
    return (sink effs, resultTy)

buildLamGeneral
  :: ScopableBuilder r m
  => NameHint -> Arrow -> Type r n
  -> (forall l.           DExt n l  => AtomName r l -> m l (EffectRow l))
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildLamGeneral hint arr ty fEff fBody = do
  withFreshBinder hint (LamBinding arr ty) \b -> do
    let v = binderName b
    effs <- fEff v
    body <- withAllowedEffects effs $ buildBlock $ fBody $ sink v
    return $ Lam $ LamExpr (LamBinder b ty arr effs) body

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: ScopableBuilder r m
                 => EmptyAbs (Nest (PiBinder r)) n
                 -> (forall l. DExt n l => [AtomName r l] -> m l (Atom r l))
                 -> m n (Atom r n)
buildPureNaryLam (EmptyAbs Empty) cont = do
  Distinct <- getDistinct
  cont []
buildPureNaryLam (EmptyAbs (Nest (PiBinder b ty arr) rest)) cont = do
  buildPureLam (getNameHint b) arr ty \x -> do
    restAbs <- sinkM $ Abs b $ EmptyAbs rest
    rest' <- applyAbs restAbs x
    buildPureNaryLam rest' \xs -> do
      x' <- sinkM x
      cont (x':xs)
buildPureNaryLam _ _ = error "impossible"

buildPi :: (Fallible1 m, Builder r m)
        => NameHint -> Arrow -> Type r n
        -> (forall l. DExt n l => AtomName r l -> m l (EffectRow l, Type r l))
        -> m n (PiType r n)
buildPi hint arr ty body = do
  withFreshPiBinder hint (PiBinding arr ty) \b -> do
    (effs, resultTy) <- body $ binderName b
    return $ PiType b effs resultTy

buildNaryPi
  :: Builder r m
  => EmptyAbs (Nest (Binder r)) n
  -> (forall l. (Distinct l, DExt n l) => [AtomName r l] -> m l (Type r l))
  -> m n (Type r n)
buildNaryPi (Abs Empty UnitE) cont = do
  Distinct <- getDistinct
  cont []
buildNaryPi (Abs (Nest (b:>ty) bs) UnitE) cont = do
  Pi <$> buildPi (getNameHint b) PlainArrow ty \v -> do
    bs' <- applySubst (b@>v) $ EmptyAbs bs
    piTy <- buildNaryPi bs' \vs -> cont $ sink v : vs
    return (Pure, piTy)

buildNonDepPi :: EnvReader m
              => NameHint -> Arrow -> Type r n -> EffectRow n -> Type r n
              -> m n (PiType r n)
buildNonDepPi hint arr argTy effs resultTy = liftBuilder do
  argTy' <- sinkM argTy
  buildPi hint arr argTy' \_ -> do
    resultTy' <- sinkM resultTy
    effs'     <- sinkM effs
    return (effs', resultTy')

buildAbs
  :: ( EnvReader m, EnvExtender m
     , SinkableE e, Color c, ToBinding binding c)
  => NameHint
  -> binding n
  -> (forall l. DExt n l => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs hint binding cont = do
  withFreshBinder hint binding \b -> do
    body <- cont $ binderName b
    return $ Abs (b:>binding) body

varsAsBinderNest :: EnvReader m => [AtomName r n] -> m n (EmptyAbs (Nest (Binder r)) n)
varsAsBinderNest [] = return $ EmptyAbs Empty
varsAsBinderNest (v:vs) = do
  rest <- varsAsBinderNest vs
  ty <- getType v
  Abs b (Abs bs UnitE) <- return $ abstractFreeVar v rest
  return $ EmptyAbs (Nest (b:>ty) bs)

typesAsBinderNest :: EnvReader m => [Type r n] -> m n (EmptyAbs (Nest (Binder r)) n)
typesAsBinderNest types = liftEnvReaderM $ go types
  where
    go :: forall r n. [Type r n] -> EnvReaderM n (EmptyAbs (Nest (Binder r)) n)
    go tys = case tys of
      [] -> return $ Abs Empty UnitE
      ty:rest -> withFreshBinder noHint ty \b -> do
        Abs bs UnitE <- go $ map sink rest
        return $ Abs (Nest (b:>ty) bs) UnitE

singletonBinderNest
  :: EnvReader m
  => NameHint -> ann n
  -> m n (EmptyAbs (Nest (BinderP AtomNameC ann)) n)
singletonBinderNest hint ann = do
  Abs b _ <- return $ newName hint
  return $ EmptyAbs (Nest (b:>ann) Empty)

buildNaryAbs
  :: ( ScopableBuilder r m, SinkableE e, SubstE Name e, SubstE (AtomSubstVal r) e, HoistableE e
     , BindsOneAtomName r b, BindsEnv b, SubstB Name b)
  => EmptyAbs (Nest b) n
  -> (forall l. DExt n l => [AtomName r l] -> m l (e l))
  -> m n (Abs (Nest b) e n)
buildNaryAbs (Abs n UnitE) body = do
  a <- liftBuilder $ buildNaryAbsRec [] n
  refreshAbs a \freshNest (ListE freshNames) ->
    Abs freshNest <$> body freshNames
{-# INLINE buildNaryAbs #-}

buildNaryAbsRec
  :: (BindsOneAtomName r b, BindsEnv b, SubstB Name b)
  => [AtomName r n] -> Nest b n l -> BuilderM r n (Abs (Nest b) (ListE (AtomName r)) n)
buildNaryAbsRec ns x = confuseGHC >>= \_ -> case x of
  Empty -> return $ Abs Empty $ ListE $ reverse ns
  Nest b bs -> do
    refreshAbs (Abs b (EmptyAbs bs)) \b' (EmptyAbs bs') -> do
      Abs bs'' ns'' <- buildNaryAbsRec (binderName b' : sinkList ns) bs'
      return $ Abs (Nest b' bs'') ns''

-- TODO: probably deprectate this version in favor of `buildNaryLamExpr`
buildNaryLam
  :: (ScopableBuilder r m, Emits n)
  => EmptyAbs (Nest (Binder r)) n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomName r l] -> m l (Atom r l))
  -> m n (Atom r n)
buildNaryLam binderNest body = do
  naryAbs <- buildNaryAbs binderNest \vs ->
    buildBlock $ body $ map sink vs
  case naryAbsToNaryLam naryAbs of
    AtomicBlock atom -> return atom
    block -> emitBlock block
  where
    naryAbsToNaryLam :: Abs (Nest (Binder r)) (Block r) n -> Block r n
    naryAbsToNaryLam (Abs binders block) = case binders of
      Empty -> block
      Nest (b:>ty) bs ->
        AtomicBlock $ Lam $ LamExpr (LamBinder b ty PlainArrow Pure) $
          naryAbsToNaryLam $ Abs bs block

asNaryLam :: EnvReader m => NaryPiType r n -> Atom r n -> m n (NaryLamExpr r n)
asNaryLam ty f = liftBuilder do
  buildNaryLamExpr ty \xs ->
    naryApp (sink f) (map Var $ toList xs)

buildNaryLamExpr
  :: ScopableBuilder r m
  => NaryPiType r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => NonEmpty (AtomName r l) -> m l (Atom r l))
  -> m n (NaryLamExpr r n)
buildNaryLamExpr (NaryPiType (NonEmptyNest b bs) eff resultTy) cont =
  case bs of
    Empty -> do
      Abs b' (PairE eff' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
        eff' <- applySubst (b@>v) eff
        result <- withAllowedEffects eff' $ buildBlock $ cont $ (sink v) :| []
        return $ PairE eff' result
      return $ NaryLamExpr (NonEmptyNest b' Empty) eff' body'
    Nest bnext rest -> do
      Abs b' lamExpr <- buildAbs (getNameHint b) (binderType b) \v -> do
        piTy' <- applySubst (b@>v) $ NaryPiType (NonEmptyNest bnext rest) eff resultTy
        buildNaryLamExpr piTy' \(v':|vs) -> cont $ sink v :| (v':vs)
      NaryLamExpr (NonEmptyNest bnext' rest') eff' body' <- return $ lamExpr
      return $ NaryLamExpr (NonEmptyNest b' (Nest bnext' rest')) eff' body'

buildAlt
  :: ScopableBuilder r m
  => Type r n
  -> (forall l. (Distinct l, Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Alt r n)
buildAlt ty body = do
  buildAbs noHint ty \x ->
    buildBlock do
      Distinct <- getDistinct
      body $ sink x

buildUnaryAtomAlt
  :: ScopableBuilder r m
  => Type r n
  -> (forall l. (Distinct l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (AltP r (Atom r) n)
buildUnaryAtomAlt ty body = do
  buildAbs noHint ty \v -> do
    Distinct <- getDistinct
    body v

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase :: (Emits n, ScopableBuilder r m)
          => Atom r n -> Type r n
          -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
          -> m n (Atom r n)
buildCase scrut resultTy indexedAltBody = do
  case trySelectBranch scrut of
    Just (i, arg) -> do
      Distinct <- getDistinct
      indexedAltBody i $ sink arg
    Nothing -> do
      scrutTy <- getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      (alts, effs) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
        (Abs b' (body `PairE` eff')) <- buildAbs noHint bTy \x -> do
          blk <- buildBlock $ indexedAltBody i $ Var $ sink x
          eff <- getEffects blk
          return $ blk `PairE` eff
        return (Abs b' body, ignoreHoistFailure $ hoist b' eff')
      liftM Var $ emit $ Case scrut alts resultTy $ mconcat effs

buildSplitCase :: (Emits n, ScopableBuilder r m)
               => LabeledItems (Type r n) -> Atom r n -> Type r n
               -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
               -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
               -> m n (Atom r n)
buildSplitCase tys scrut resultTy match fallback = do
  split <- emitOp $ VariantSplit tys scrut
  buildCase split resultTy \i v ->
    case i of
      0 -> match v
      1 -> fallback v
      _ -> error "should only have two cases"

buildEffLam
  :: ScopableBuilder r m
  => RWS -> NameHint -> Type r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildEffLam rws hint ty body = do
  eff <- getAllowedEffects
  buildLam noHint PlainArrow TyKind Pure \h -> do
    let ty' = RefTy (Var h) (sink ty)
    withFreshBinder hint (LamBinding PlainArrow ty') \b -> do
      let ref = binderName b
      h' <- sinkM h
      let eff' = extendEffect (RWSEffect rws (Just h')) (sink eff)
      body' <- withAllowedEffects eff' $ buildBlock $ body (sink h) $ sink ref
      -- Contract the type of the produced function to only mention
      -- the effects actually demanded by the body.  This is safe because
      -- it's immediately consumed by an effect discharge primitive.
      effs <- getEffects body'
      return $ Lam $ LamExpr (LamBinder b ty' PlainArrow effs) body'

buildForAnn
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> ForAnn -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForAnn hint ann ixTy@(IxType iTy ixDict) body = do
  lam <- withFreshBinder hint ixTy \b -> do
    let v = binderName b
    body' <- buildBlock $ body $ sink v
    effs <- getEffects body'
    return $ Lam $ LamExpr (LamBinder b iTy PlainArrow effs) body'
  liftM Var $ emit $ Hof $ For ann ixDict lam

buildFor :: (Emits n, ScopableBuilder r m)
         => NameHint -> Direction -> IxType r n
         -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
         -> m n (Atom r n)
buildFor hint dir ty body = buildForAnn hint dir ty body

unzipTab :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n, Atom r n)
unzipTab tab = do
  TabTy (_:>ixTy) _ <- getType tab
  fsts <- liftEmitBuilder $ buildTabLam noHint ixTy \i ->
            liftM fst $ tabApp (sink tab) (Var i) >>= fromPair
  snds <- liftEmitBuilder $ buildTabLam noHint ixTy \i ->
            liftM snd $ tabApp (sink tab) (Var i) >>= fromPair
  return (fsts, snds)

emitRunWriter
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Type r n -> BaseMonoid r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunWriter hint accTy bm body = do
  lam <- buildEffLam Writer hint accTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunWriter Nothing bm lam

emitRunState
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunState hint initVal body = do
  stateTy <- getType initVal
  lam <- buildEffLam State hint stateTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunState Nothing initVal lam

emitRunReader
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunReader hint r body = do
  rTy <- getType r
  lam <- buildEffLam Reader hint rTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunReader r lam

-- === vector space (ish) type class ===

zeroAt :: HasCallStack => Builder r m => Type r n -> m n (Atom r n)
zeroAt ty = case ty of
  BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
  ProdTy tys -> ProdVal <$> mapM zeroAt tys
  StaticRecordTy tys -> Record tys <$> mapM zeroAt (toList tys)
  TabTy (b:>ixTy) bodyTy ->
    liftEmitBuilder $ buildTabLam (getNameHint b) ixTy \i ->
      zeroAt =<< applySubst (b@>i) bodyTy
  _ -> unreachable
  where
    unreachable :: a
    unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
    zeroLit bt = case bt of
      Scalar Float64Type -> Float64Lit 0.0
      Scalar Float32Type -> Float32Lit 0.0
      _                  -> unreachable

zeroLike :: (HasCallStack, HasType r e, Builder r m) => e n -> m n (Atom r n )
zeroLike x = zeroAt =<< getType x

tangentType :: EnvReader m => Type r n -> m n (Type r n)
tangentType ty = maybeTangentType ty >>= \case
  Just tanTy -> return tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: EnvReader m => Type r n -> m n (Maybe (Type r n))
maybeTangentType ty = liftEnvReaderT $ maybeTangentType' ty

maybeTangentType' :: Type r n -> EnvReaderT Maybe n (Type r n)
maybeTangentType' ty = case ty of
  StaticRecordTy items -> StaticRecordTy <$> mapM rec items
  -- TODO: Delete this case! This is a hack!
  TypeCon _ _ _ -> rec =<< fromNewtypeWrapper ty
  TabTy b bodyTy -> do
    refreshAbs (Abs b bodyTy) \b' bodyTy' -> do
      bodyTanTy <- rec bodyTy'
      return $ TabTy b' bodyTanTy
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> return $ TC con
    BaseType (Scalar Float32Type) -> return $ TC con
    BaseType   _                  -> return $ UnitTy
    Nat                           -> return $ UnitTy
    Fin _                         -> return $ UnitTy
    ProdType   tys                -> ProdTy <$> traverse rec tys
    _ -> empty
  _ -> empty
  where rec = maybeTangentType'

fromNewtypeWrapper :: (EnvReader m, Fallible1 m) => Type r n -> m n (Type r n)
fromNewtypeWrapper ty = do
  TypeCon _ defName params <- return ty
  def <- lookupDataDef defName
  [con] <- instantiateDataDef def params
  -- Single field constructors are represented by their field
  DataConDef _ wrappedTy [_] <- return con
  return $ unsafeCoerceIRE wrappedTy

tangentBaseMonoidFor :: Builder r m => Type r n -> m n (BaseMonoid r n)
tangentBaseMonoidFor ty = do
  zero <- zeroAt ty
  adder <- liftEmitBuilder $ buildLam noHint PlainArrow ty Pure \v -> updateAddAt $ Var v
  return $ BaseMonoid zero adder

addTangent :: (Emits n, Builder r m) => Atom r n -> Atom r n -> m n (Atom r n)
addTangent x y = do
  getType x >>= \case
    StaticRecordTy tys -> do
      elems <- bindM2 (zipWithM addTangent) (getUnpacked x) (getUnpacked y)
      return $ Record tys elems
    TabTy (b:>ixTy) _  ->
      liftEmitBuilder $ buildFor (getNameHint b) Fwd ixTy \i -> do
        bindM2 addTangent (tabApp (sink x) (Var i)) (tabApp (sink y) (Var i))
    TC con -> case con of
      BaseType (Scalar _) -> emitOp $ BinOp FAdd x y
      ProdType _          -> do
        xs <- getUnpacked x
        ys <- getUnpacked y
        ProdVal <$> zipWithM addTangent xs ys
      ty -> notTangent ty
    ty -> notTangent ty
    where notTangent ty = error $ "Not a tangent type: " ++ pprint ty

updateAddAt :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
updateAddAt x = liftEmitBuilder do
  ty <- getType x
  buildLam noHint PlainArrow ty Pure \v -> addTangent (sink x) (Var v)

-- === builder versions of common top-level emissions ===

emitDataDef :: (Mut n, TopBuilder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef
  where hint = getNameHint sourceName

emitEffectDef :: (Mut n, TopBuilder m) => EffectDef n -> m n (EffectName n)
emitEffectDef effectDef@(EffectDef name _) =
  emitBinding (getNameHint name) $ EffectBinding effectDef

emitHandlerDef :: (Mut n, TopBuilder m) => SourceName -> HandlerDef n -> m n (HandlerName n)
emitHandlerDef name handlerDef =
  emitBinding (getNameHint name) $ HandlerBinding handlerDef

emitEffectOpDef :: (Mut n, TopBuilder m) => EffectName n -> Int -> SourceName -> m n (Name EffectOpNameC n)
emitEffectOpDef effName i opName = do
  let hint = getNameHint opName
  let opDef = EffectOpDef effName (OpIdx i)
  emitBinding hint $ EffectOpBinding opDef

emitClassDef :: (Mut n, TopBuilder m) => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _ _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _) = do
  emitBinding (getNameHint className) $ InstanceBinding instanceDef

emitDataConName :: (Mut n, TopBuilder m) => DataDefName n -> Int -> Atom r n -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx conAtom = do
  DataDef _ _ dataCons <- lookupDataDef dataDefName
  let (DataConDef name _ _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx (unsafeCoerceIRE conAtom)

zipNest :: (forall ii ii'. a -> b ii ii' -> b' ii ii')
        -> [a]
        -> Nest b  i i'
        -> Nest b' i i'
zipNest _ _ Empty = Empty
zipNest f (x:t) (Nest b rest) = Nest (f x b) $ zipNest f t rest
zipNest _ _ _ = error "List too short!"

emitMethod
  :: (Mut n, TopBuilder m)
  => NameHint -> ClassName n -> [Bool] -> Int -> m n (Name MethodNameC n)
emitMethod hint classDef explicit idx = do
  getter <- makeMethodGetter classDef explicit idx
  f <- Var <$> emitTopLet hint PlainLet (Atom getter)
  emitBinding hint $ MethodBinding classDef idx f

makeMethodGetter :: EnvReader m => Name ClassNameC n -> [Bool] -> Int -> m n (Atom r n)
makeMethodGetter className explicit methodIdx = liftBuilder do
  className' <- sinkM className
  ClassDef sourceName _ paramBs _ _ <- getClassDef className'
  let arrows = explicit <&> \case True -> PlainArrow; False -> ImplicitArrow
  buildPureNaryLam (EmptyAbs $ zipPiBinders arrows paramBs) \params -> do
    let dictTy = DictTy $ DictType sourceName (sink className') (map Var params)
    buildPureLam noHint ClassArrow dictTy \dict ->
      emitOp $ ProjMethod (Var dict) methodIdx
  where
    zipPiBinders :: [Arrow] -> Nest (RolePiBinder r') i i' -> Nest (PiBinder r) i i'
    zipPiBinders = zipNest \arr (RolePiBinder b ty _ _) -> PiBinder b (unsafeCoerceIRE ty) arr

emitTyConName :: (Mut n, TopBuilder m) => DataDefName n -> Atom r n -> m n (Name TyConNameC n)
emitTyConName dataDefName tyConAtom = do
  let tyConAtom' = unsafeCoerceIRE tyConAtom
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName tyConAtom'

getDataCon :: EnvReader m => Name DataConNameC n -> m n (DataDefName n, Int)
getDataCon v = do
  ~(DataConBinding defName idx _) <- lookupEnv v
  return (defName, idx)

getClassDef :: EnvReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef) <- lookupEnv classDefName
  return classDef

-- === builder versions of common local ops ===

fLitLike :: (Builder r m, Emits n) => Double -> Atom r n -> m n (Atom r n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
neg x = emitOp $ UnOp FNeg x

add :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
add x y = emitOp $ BinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ BinOp IAdd x y

mul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
mul x y = emitOp $ BinOp FMul x y

imul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ BinOp IMul x y

sub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
sub x y = emitOp $ BinOp FSub x y

isub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ BinOp ISub x y

select :: (Builder r m, Emits n) => Atom r n -> Atom r n -> Atom r n -> m n (Atom r n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
div' x y = emitOp $ BinOp FDiv x y

idiv :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ BinOp IDiv x y

irem :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
irem x y = emitOp $ BinOp IRem x y

fpow :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
fpow x y = emitOp $ BinOp FPow x y

flog :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
flog x = emitOp $ UnOp Log x

ilt :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ BinOp (ICmp Less) x y

ieq :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ BinOp (ICmp Equal) x y

fromPair :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n, Atom r n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getProj :: (Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
getFst p = fst <$> fromPair p

getSnd :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: (Builder r m, Emits n) => [Int] -> Atom r n -> m n (Atom r n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: (Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
getProjRef i r = emitOp $ ProjRef i r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, EnvReader m) => Atom r n -> m n [Atom r n]
getUnpacked atom = do
  atom' <- cheapNormalize atom
  ty <- getType atom'
  idxs <- projectionIndices ty
  return $ idxs <&> flip getProjection atom'
{-# SCC getUnpacked #-}

emitUnpacked :: (Builder r m, Emits n) => Atom r n -> m n [AtomName r n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

unwrapBaseNewtype :: Atom r n -> Atom r n
unwrapBaseNewtype = getProjection [UnwrapBaseNewtype]
{-# INLINE unwrapBaseNewtype #-}

unwrapCompoundNewtype :: Atom r n -> Atom r n
unwrapCompoundNewtype = getProjection [UnwrapCompoundNewtype]
{-# INLINE unwrapCompoundNewtype #-}

app :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
app x i = Var <$> emit (App x (i:|[]))

naryApp :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryApp = naryAppHinted noHint
{-# INLINE naryApp #-}

naryAppHinted :: (Builder r m, Emits n)
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryAppHinted hint f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emitHinted hint (App f xs')

tabApp :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
tabApp x i = Var <$> emit (TabApp x (i:|[]))

naryTabApp :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabApp = naryTabAppHinted noHint
{-# INLINE naryTabApp #-}

naryTabAppHinted :: (Builder r m, Emits n)
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabAppHinted hint f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emitHinted hint (TabApp f xs')

indexRef :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
indexRef ref i = emitOp $ IndexRef ref i

naryIndexRef :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
unsafePtrLoad x = do
  lam <- liftEmitBuilder $ buildLam noHint PlainArrow UnitTy (OneEffect IOEffect) \_ ->
    emitOp . PtrLoad =<< sinkM x
  liftM Var $ emit $ Hof $ RunIO $ lam

-- === index set type class ===

-- XXX: it's important that we do the reduction here, because we need the
-- property that if we call this with a simplified dict, we only produce
-- simplified decls.
applyIxMethod :: (Builder r m, Emits n) => Atom r n -> IxMethod -> [Atom r n] -> m n (Atom r n)
applyIxMethod dict method args = case dict of
  DictCon (IxFin n) -> case method of
    Size -> do
      [] <- return args
      return n                       -- result : Nat
    Ordinal -> do
      [ix] <- return args            -- ix : Fin n
      return $ unwrapBaseNewtype ix  -- result : Nat
    UnsafeFromOrdinal -> do
      [ix] <- return args                     -- ix : Nat
      return $ Con $ Newtype (TC $ Fin n) ix  -- result : Fin n
  DictCon (ExplicitMethods d params) -> do
    SpecializedDictBinding (SpecializedDict _ (Just fs)) <- lookupEnv d
    NaryLamExpr bs _ body <- return $ unsafeCoerceIRE $ fs !! fromEnum method
    let args' = case method of
          Size -> params ++ [UnitVal]
          _    -> params ++ args
    emitBlock =<< applySubst (bs @@> fmap SubstVal args') body
  _ -> do
    methodImpl <- emitOp $ ProjMethod dict (fromEnum method)
    naryApp methodImpl args

-- This works with `Nat` instead of `IndexRepTy` because it's used alongside
-- user-defined instances.
projectIxFinMethod :: EnvReader m => IxMethod -> Atom r n -> m n (Atom r n)
projectIxFinMethod method n = liftBuilder do
  case method of
    Size -> return n  -- result : Nat
    Ordinal -> buildPureLam noHint PlainArrow (TC $ Fin n) \ix ->
      return $ unwrapBaseNewtype (Var ix) -- result : Nat
    UnsafeFromOrdinal -> buildPureLam noHint PlainArrow NatTy \ix ->
      return $ Con $ Newtype (TC $ Fin $ sink n) $ Var ix

-- XXX: these internal versions of `ordinal`, `unsafeFromOrdinal` and
-- `indexSetSize`. work with `IdxRepTy` (whereas the user-facing versions work
-- with `Nat`)
unsafeFromOrdinal :: forall r m n. (Builder r m, Emits n) => IxType r n -> Atom r n -> m n (Atom r n)
unsafeFromOrdinal (IxType _ dict) i = applyIxMethod dict UnsafeFromOrdinal [repToNat i]

ordinal :: forall r m n. (Builder r m, Emits n) => IxType r n -> Atom r n -> m n (Atom r n)
ordinal (IxType _ dict) idx = do
  unwrapBaseNewtype <$> applyIxMethod dict Ordinal [idx]

indexSetSize :: (Builder r m, Emits n) => IxType r n -> m n (Atom r n)
indexSetSize (IxType _ dict) = do
  sizeNat <- applyIxMethod dict Size []
  return $ unwrapBaseNewtype sizeNat

repToNat :: Atom r n -> Atom r n
repToNat x = Con $ Newtype NatTy x
{-# INLINE repToNat #-}

-- === pseudo-prelude ===

-- Bool -> (Unit -> {|eff} a) -> (() -> {|eff} a) -> {|eff} a
-- XXX: the first argument is the true case, following the
-- surface-level `if ... then ... else ...`, but the order
-- is flipped in the actual `Case`, because False acts like 0.
-- TODO: consider a version that figures out the result type itself.
emitIf :: (Emits n, ScopableBuilder r m)
       => Atom r n
       -> Type r n
       -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
       -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
       -> m n (Atom r n)
emitIf predicate resultTy trueCase falseCase = do
  predicate' <- emitOp $ ToEnum (SumTy [UnitTy, UnitTy]) predicate
  buildCase predicate' resultTy \i _ ->
    case i of
      0 -> falseCase
      1 -> trueCase
      _ -> error "should only have two cases"

emitMaybeCase :: (Emits n, ScopableBuilder r m)
              => Atom r n -> Type r n
              -> (forall l. (Emits l, DExt n l) =>             m l (Atom r l))
              -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
              -> m n (Atom r n)
emitMaybeCase scrut resultTy nothingCase justCase = do
  buildCase scrut resultTy \i v ->
    case i of
      0 -> nothingCase
      1 -> justCase v
      _ -> error "should be a binary scrutinee"

-- Maybe a -> a
fromJustE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
fromJustE x = liftEmitBuilder do
  MaybeTy a <- getType x
  emitMaybeCase x a
    (emitOp $ ThrowError $ sink a)
    (return)

-- Maybe a -> Bool
isJustE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
isJustE x = liftEmitBuilder $
  emitMaybeCase x BoolTy (return FalseAtom) (\_ -> return TrueAtom)

-- Monoid a -> (n=>a) -> a
reduceE :: (Emits n, Builder r m) => BaseMonoid r n -> Atom r n -> m n (Atom r n)
reduceE monoid xs = liftEmitBuilder do
  TabTy (n:>ty) a <- getType xs
  a' <- return $ ignoreHoistFailure $ hoist n a
  getSnd =<< emitRunWriter noHint a' monoid \_ ref ->
    buildFor noHint Fwd (sink ty) \i -> do
      x <- tabApp (sink xs) (Var i)
      emitOp $ PrimEffect (sink $ Var ref) $ MExtend (fmap sink monoid) x

andMonoid :: EnvReader m => m n (BaseMonoid r n)
andMonoid =  liftM (BaseMonoid TrueAtom) do
  liftBuilder $
    buildLam noHint PlainArrow BoolTy Pure \x ->
      buildLam noHint PlainArrow BoolTy Pure \y -> do
        emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: (Emits n, ScopableBuilder r m)
     => (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
     -> Atom r n -> m n (Atom r n)
mapE f xs = do
  TabTy (n:>ty) _ <- getType xs
  buildFor (getNameHint n) Fwd ty \i -> do
    x <- tabApp (sink xs) (Var i)
    f x

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
catMaybesE maybes = do
  TabTy n (MaybeTy a) <- getType maybes
  justs <- liftEmitBuilder $ mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy n a)
    (JustAtom (sink $ TabTy n a) <$> mapE fromJustE (sink maybes))
    (return (NothingAtom $ sink $ TabTy n a))

emitWhile :: (Emits n, ScopableBuilder r m)
          => (forall l. (Emits l, DExt n l) => m l (Atom r l))
          -> m n ()
emitWhile body = do
  eff <- getAllowedEffects
  lam <- buildNullaryLam eff body
  void $ emit $ Hof $ While lam

-- Dex implementation, for reference
-- def whileMaybe (eff:Effects) -> (body: Unit -> {|eff} (Maybe Word8)) : {|eff} Maybe Unit =
--   hadError = yieldState False \ref.
--     while do
--       ans = liftState ref body ()
--       case ans of
--         Nothing ->
--           ref := True
--           False
--         Just cond -> W8ToB cond
--   if hadError
--     then Nothing
--     else Just ()

runMaybeWhile :: (Emits n, ScopableBuilder r m)
              => (forall l. (Emits l, DExt n l) => m l (Atom r l))
              -> m n (Atom r n)
runMaybeWhile body = do
  hadError <- getSnd =<< emitRunState noHint FalseAtom \_ ref -> do
    emitWhile do
      ans <- body
      emitMaybeCase ans Word8Ty
        (emitOp (PrimEffect (sink $ Var ref) $ MPut TrueAtom) >> return FalseAtom)
        (return)
    return UnitVal
  emitIf hadError (MaybeTy UnitTy)
    (return $ NothingAtom UnitTy)
    (return $ JustAtom    UnitTy UnitVal)

-- === capturing closures with telescopes ===

type ReconAbs e n = NaryAbs AtomNameC e n
data ReconstructAtom (r::IR) (n::S) =
   IdentityRecon
 | LamRecon (ReconAbs (Atom r) n)

applyRecon :: (EnvReader m, Fallible1 m)
           => ReconstructAtom r n -> Atom r n -> m n (Atom r n)
applyRecon IdentityRecon x = return x
applyRecon (LamRecon ab) x = applyReconAbs ab x

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE (AtomSubstVal r) e)
  => ReconAbs e n -> Atom r n -> m n (e n)
applyReconAbs ab x = do
  xs <- unpackTelescope x
  applyNaryAbs ab $ map SubstVal xs

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b)
  => b n l -> e l -> m l (Atom r l, Type r n, ReconAbs e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- mapM (getType . Var) vs
  let (vsSorted, tys) = unzip $ toposortAnnVars $ zip vs vTys
  ty <- liftEnvReaderM $ buildTelescopeTy vs tys
  result <- buildTelescopeVal (map Var vsSorted) ty
  let ty' = ignoreHoistFailure $ hoist bs ty
  let ab  = ignoreHoistFailure $ hoist bs $ abstractFreeVarsNoAnn vsSorted e
  return (result, ty', ab)

-- XXX: assumes arguments are toposorted
buildTelescopeTy :: (EnvReader m, EnvExtender m)
                 => [AtomName r n] -> [Type r n] -> m n (Type r n)
buildTelescopeTy [] [] = return UnitTy
buildTelescopeTy (v:vs) (ty:tys) = do
  withFreshBinder (getNameHint v) (MiscBound ty) \b -> do
    ListE tys' <- applyAbs (sink $ abstractFreeVar v $ ListE tys) (binderName b)
    ListE vs' <- sinkM $ ListE vs
    innerTelescope <- buildTelescopeTy vs' tys'
    return case hoist b innerTelescope of
      HoistSuccess innerTelescope' -> PairTy ty innerTelescope'
      HoistFailure _ -> DepPairTy $ DepPairType (b:>ty) innerTelescope
buildTelescopeTy _ _ = error "zip mismatch"

buildTelescopeVal :: EnvReader m => [Atom r n] -> Type r n -> m n (Atom r n)
buildTelescopeVal elts telescopeTy = go elts telescopeTy
  where
    go :: (EnvReader m) => [Atom r n] -> Type r n -> m n (Atom r n)
    go [] UnitTy = return UnitVal
    go (x:xs) (PairTy _ xsTy) = do
      rest <- go xs xsTy
      return $ PairVal x rest
    go (x:xs) (DepPairTy ty) = do
      xsTy <- instantiateDepPairTy ty x
      rest <- go xs xsTy
      return $ DepPair x rest ty
    go _ _ = error "zip mismatch"

-- sorts name-annotation pairs so that earlier names may be occur free in later
-- annotations but not vice versa.
toposortAnnVars :: forall e c n. (Color c, HoistableE e)
                => [(Name c n, e n)] -> [(Name c n, e n)]
toposortAnnVars annVars =
  let (graph, vertexToNode, _) = graphFromEdges $ map annVarToNode annVars
  in map (nodeToAnnVar . vertexToNode) $ reverse $ topSort graph
  where
    annVarToNode :: (Name c n, e n) -> (e n, Name c n, [Name c n])
    annVarToNode (v, ann) = (ann, v, nameSetToList $ freeVarsE ann)

    nodeToAnnVar :: (e n, Name c n, [Name c n]) -> (Name c n, e n)
    nodeToAnnVar (ann, v, _) = (v, ann)

unpackTelescope :: (Fallible1 m, EnvReader m) => Atom r n -> m n [Atom r n]
unpackTelescope atom = do
  n <- telescopeLength <$> getType atom
  return $ go n atom
  where
    go :: Int -> Atom r n -> [Atom r n]
    go 0 _ = []
    go n pair = left : go (n-1) right
      where left  = getProjection [ProjectProduct 0] pair
            right = getProjection [ProjectProduct 1] pair

    telescopeLength :: Type r n -> Int
    telescopeLength ty = case ty of
      UnitTy -> 0
      PairTy _ rest -> 1 + telescopeLength rest
      DepPairTy (DepPairType _ rest) -> 1 + telescopeLength rest
      _ -> error $ "not a valid telescope: " ++ pprint ty

-- gives a list of atom names that are free in `e`, including names mentioned in
-- the types of those names, recursively.
localVarsAndTypeVars
  :: forall m b e n l.
     (EnvReader m, BindsNames b, HoistableE e)
  => b n l -> e l -> m l [Name AtomNameC l]
localVarsAndTypeVars b e =
  transitiveClosureM varsViaType (localVars b e)
  where
    varsViaType :: Name AtomNameC l -> m l [Name AtomNameC l]
    varsViaType v = do
      ty <- getType $ Var v
      return $ localVars b ty

localVars :: (Color c, BindsNames b, HoistableE e)
          => b n l -> e l -> [Name c l]
localVars b e = nameSetToList $
  R.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

instance GenericE (ReconstructAtom r) where
  type RepE (ReconstructAtom r) = EitherE UnitE (NaryAbs AtomNameC (Atom r))
  fromE IdentityRecon = LeftE UnitE
  fromE (LamRecon recon) = RightE recon
  toE (LeftE _) = IdentityRecon
  toE (RightE recon) = LamRecon recon

instance SinkableE   (ReconstructAtom r)
instance HoistableE  (ReconstructAtom r)
instance AlphaEqE    (ReconstructAtom r)
instance SubstE Name (ReconstructAtom r)
instance SubstE (AtomSubstVal r) (ReconstructAtom r)

instance Pretty (ReconstructAtom r n) where
  pretty IdentityRecon = "Identity reconstruction"
  pretty (LamRecon ab) = "Reconstruction abs: " <> pretty ab

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: BuilderM r n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
