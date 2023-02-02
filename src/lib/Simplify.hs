-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Simplify
  ( simplifyTopBlock, simplifyTopFunction, SimplifiedBlock (..), ReconstructAtom (..), applyReconTop,
    emitSpecialization, linearizeTopFun) where

import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.List (elemIndex)
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import qualified Data.List.NonEmpty as NE
import GHC.Exts (inline)

import Builder
import CheapReduction
import CheckType (CheckableE (..), isData)
import Core
import Err
import Generalize
import IRVariants
import LabeledItems
import Linearize
import Name
import Subst
import Optimize (peepholeOp)
import QueryType
import RuntimePrint
import Transpose
import Types.Core
import Types.Primitives
import Util (enumerate, foldMapM, restructure, splitAtExact, bindM2)

-- === Simplification ===

-- The purpose of simplification is that we want first-class functions
-- in the surface language, but we don't want to deal with them when
-- generating code.  To that end, simplification inlines almost all
-- functions everywhere they appear.

-- In particular, simplification also carries out AD by discharging
-- the `Linearize` and `Transpose` constructors of `PrimHof`.

-- The exception is functions explicitly tagged @noinline by the
-- programmer.  Those, however, are second-class: they are all
-- toplevel, and get specialized until they are first order.

-- Currently, simplification also discharges `CatchException` by
-- elaborating the expression into a Maybe-style monad.  Note: the
-- plan is for `CatchException` to become a user-defined effect, and
-- for simplification to discharge all of them.

-- Simplification also discharges bulk record and variant operations
-- by converting them into individual projections and constructors.

-- Simplification also opportunistically does peep-hole optimizations:
-- some constant folding, case-of-known-constructor, projecting known
-- elements from products, etc; but is not guaranteed to find all such
-- opportunities.

-- === Conversions between CoreIR, CoreToSimpIR, SimpIR ===

-- lift a Simp data atom to a CoreToSimp atom with an optional newtype-coercion
liftSimpAtom
  :: (MonadFail1 m, EnvReader m)
  => Maybe (Type CoreIR n) -> SAtom n -> m n (CAtom n)
liftSimpAtom maybeTy simpAtom = case maybeTy of
  Nothing -> liftPlainSimpAtom simpAtom
  Just ty -> liftSimpAtomWithType ty simpAtom

liftPlainSimpAtom :: (MonadFail1 m, EnvReader m) => SAtom n -> m n (CAtom n)
liftPlainSimpAtom = \case
  Var v -> return $ SimpInCore $ LiftSimp Nothing $ Var v
  Con con -> Con <$> case con of
    Lit v -> return $ Lit v
    ProdCon xs -> ProdCon <$> mapM rec xs
    SumCon ts i x -> SumCon <$> mapM liftSimpType ts <*> pure i <*> rec x
    _ -> error $ "not implemented: " ++ pprint con
  atom -> error $ "not a data atom: " ++ pprint atom
  where rec = liftPlainSimpAtom

liftSimpType :: (MonadFail1 m, EnvReader m) => SType n -> m n (CType n)
liftSimpType = \case
  BaseTy t -> return $ BaseTy t
  ProdTy ts -> ProdTy <$> mapM rec ts
  SumTy  ts -> SumTy  <$> mapM rec ts
  t -> error $ "not implemented: " ++ pprint t
  where rec = liftSimpType

liftSimpAtomWithType :: (MonadFail1 m, EnvReader m) => Type CoreIR n -> SAtom n -> m n (CAtom n)
liftSimpAtomWithType ty simpAtom = case simpAtom of
  Var _          -> justLift
  ProjectElt _ _ -> justLift
  _ -> do
    (cons , ty') <- unwrapLeadingNewtypesType ty
    atom <- case (ty', simpAtom) of
      (BaseTy _  , Con (Lit v))      -> return $ Con $ Lit v
      (ProdTy tys, Con (ProdCon xs))   -> Con . ProdCon <$> zipWithM rec tys xs
      (SumTy  tys, Con (SumCon _ i x)) -> Con . SumCon tys i <$> rec (tys!!i) x
      (DepPairTy dpt@(DepPairType (b:>t1) t2), DepPair x1 x2 _) -> do
        x1' <- rec t1 x1
        t2' <- applySubst (b@>SubstVal x1') t2
        x2' <- rec t2' x2
        return $ DepPair x1' x2' dpt
      _ -> error $ "can't lift " <> pprint simpAtom <> " to " <> pprint ty'
    return $ wrapNewtypesData cons atom
  where
    rec = liftSimpAtomWithType
    justLift = return $ SimpInCore $ LiftSimp (Just ty) simpAtom

liftSimpFun
  :: (MonadFail1 m, EnvReader m)
  => Type CoreIR n -> LamExpr SimpIR n -> m n (CAtom n)
liftSimpFun (Pi piTy) f = return $ SimpInCore $ LiftSimpFun piTy f
liftSimpFun _ _ = error "not a pi type"

-- `Nothing` (the `Maybe (Type CoreIR)` one) means that there's no newtype coercion
-- needed to get back to the original atom.
tryAsDataAtom :: Emits n => CAtom n -> SimplifyM i n (Maybe (SAtom n, Maybe (Type CoreIR n)))
tryAsDataAtom atom = do
  ty <- getType atom
  isData ty >>= \case
    False -> return Nothing
    True -> Just <$> do
      repAtom <- go atom
      return (repAtom, Just ty)
 where
  go :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
  go = \case
    Var _ -> error "Shouldn't have core variables left" -- need to handle top-level vars?
    Con con -> Con <$> case con of
      Lit v -> return $ Lit v
      ProdCon xs -> ProdCon <$> mapM go xs
      SumCon  tys tag x -> SumCon <$> mapM getRepType tys <*> pure tag <*> go x
      SumAsProd tys tag xs ->
        SumAsProd <$> mapM getRepType tys <*> go tag <*> mapM go xs
      DictHole _ _ -> error "unexpected DictHole"
      HeapVal       -> return HeapVal
    PtrVar v        -> return $ PtrVar v
    DepPair x y ty -> do
      DepPairTy ty' <- getRepType $ DepPairTy ty
      DepPair <$> go x <*> go y <*> pure ty'
    ProjectElt UnwrapNewtype x -> go x
    -- TODO: do we need to think about a case like `fst (1, \x.x)`, where
    -- the projection is data but the argument isn't?
    ProjectElt (ProjectProduct i) x -> normalizeProj (ProjectProduct i) =<< go x
    NewtypeCon _ x  -> go x
    SimpInCore x    -> case x of
      LiftSimp _ x' -> return x'
      LiftSimpFun _ _ -> notData
      TabLam _ tabLam -> forceTabLam tabLam
      ACase scrut alts resultTy -> forceACase scrut alts resultTy
    Lam _ _   _     -> notData
    DepPairTy _     -> notData
    Pi _            -> notData
    NewtypeTyCon _  -> notData
    DictCon _       -> notData
    DictTy _        -> notData
    Eff _           -> notData
    TC _            -> notData
    TabPi _         -> notData
    where
      notData = error $ "Not runtime-representable data: " ++ pprint atom

forceTabLam :: Emits n => TabLamExpr n -> SimplifyM i n (SAtom n)
forceTabLam (Abs (b:>ixTy) ab) =
  buildFor (getNameHint b) Fwd ixTy \v -> do
    Abs decls result <- applyRename (b@>v) ab
    result' <- emitDecls decls result
    toDataAtomIgnoreRecon result'

forceACase :: Emits n => SAtom n -> [Abs SBinder CAtom n] -> CType n -> SimplifyM i n (SAtom n)
forceACase scrut alts resultTy = do
  resultTy' <- getRepType  resultTy
  buildCase scrut resultTy' \i arg -> do
    Abs b result <- return $ alts !! i
    applySubst (b@>SubstVal arg) result >>= toDataAtomIgnoreRecon

tryGetRepType :: Type CoreIR n -> SimplifyM i n (Maybe (SType n))
tryGetRepType t = isData t >>= \case
  False -> return Nothing
  True  -> Just <$> getRepType t

getRepType :: Type CoreIR n -> SimplifyM i n (SType n)
getRepType ty = go ty where
  go :: Type CoreIR n -> SimplifyM i n (SType n)
  go = \case
    TC con -> TC <$> case con of
      BaseType b  -> return $ BaseType b
      ProdType ts -> ProdType <$> mapM go ts
      SumType  ts -> SumType  <$> mapM go ts
      RefType h a -> RefType  <$> toDataAtomIgnoreReconAssumeNoDecls h <*> go a
      TypeKind    -> error $ notDataType
      HeapType    -> return $ HeapType
    DepPairTy (DepPairType b@(_:>l) r) -> do
      l' <- go l
      withFreshBinder (getNameHint b) l' \b' -> do
        x <- liftSimpAtom (Just $ sink l) (Var $ binderName b')
        r' <- go =<< applySubst (b@>SubstVal x) r
        return $ DepPairTy $ DepPairType (b':>l') r'
    TabPi (TabPiType (b:>ixTy) bodyTy) -> do
      ixTy' <- simplifyIxType ixTy
      withFreshBinder (getNameHint b) ixTy' \b' -> do
        x <- liftSimpAtom (Just $ sink $ ixTypeType ixTy) (Var $ binderName b')
        bodyTy' <- go =<< applySubst (b@>SubstVal x) bodyTy
        return $ TabPi $ TabPiType (b':>ixTy') bodyTy'
    NewtypeTyCon con -> do
      (_, ty') <- unwrapNewtypeType con
      go ty'
    Pi _           -> error notDataType
    DictTy _       -> error notDataType
    DictCon _      -> error notType
    Eff _          -> error notType
    Con _          -> error notType
    PtrVar _       -> error notType
    DepPair _ _ _  -> error notType
    ProjectElt _ _ -> error notType
    NewtypeCon _ _ -> error notType
    SimpInCore _   -> error notType
    Lam _ _   _    -> error notType
    Var _ -> error "Shouldn't have type variables in CoreIR IR with SimpIR builder names"
    where
      notType     = "Not a type: " ++ pprint ty
      notDataType = "Not a type of runtime-representable data: " ++ pprint ty

toDataAtom :: Emits n => CAtom n -> SimplifyM i n (SAtom n, Maybe (Type CoreIR n))
toDataAtom x = tryAsDataAtom x >>= \case
  Just x' -> return x'
  Nothing -> error $ "Not a data atom: " ++ pprint x

toDataAtomIgnoreRecon :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreRecon x = fst <$> toDataAtom x

toDataAtomIgnoreReconAssumeNoDecls :: CAtom n -> SimplifyM i n (SAtom n)
toDataAtomIgnoreReconAssumeNoDecls x = do
  Abs decls result <- buildScoped $ fst <$> toDataAtom (sink x)
  case decls of
    Empty -> return result
    _ -> error "unexpected decls"

toDataOrRepType :: Emits n => CAtom n -> SimplifyM i n (SAtom n)
toDataOrRepType x = getType x >>= \case
  TyKind -> getRepType x
  _ -> toDataAtomIgnoreRecon x

withSimplifiedBinders
 :: Nest (Binder CoreIR) o any
 -> (forall o'. DExt o o' => Nest (Binder SimpIR) o o' -> [CAtom o'] -> SimplifyM i o' a)
 -> SimplifyM i o a
withSimplifiedBinders Empty cont = getDistinct >>= \Distinct -> cont Empty []
withSimplifiedBinders (Nest (bCore:>ty) bsCore) cont = do
  simpTy <- getRepType ty
  withFreshBinder (getNameHint bCore) simpTy \bSimp -> do
    x <- liftSimpAtom (Just $ sink ty) (Var $ binderName bSimp)
    -- TODO: carry a substitution instead of doing N^2 work like this
    Abs bsCore' UnitE <- applySubst (bCore@>SubstVal x) (EmptyAbs bsCore)
    withSimplifiedBinders bsCore' \bsSimp xs ->
      cont (Nest (bSimp:>simpTy) bsSimp) (sink x:xs)

-- === Reconstructions ===

data ReconstructAtom (n::S) =
   CoerceRecon (Type CoreIR n)
 | LamRecon (ReconAbs SimpIR CAtom n)

applyRecon :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyRecon (CoerceRecon ty) x = liftSimpAtom (Just ty) x
applyRecon (LamRecon ab) x = applyReconAbs ab x

-- === Simplification monad ===

class (ScopableBuilder2 SimpIR m, SubstReader AtomSubstVal m) => Simplifier m

newtype SimplifyM (i::S) (o::S) (a:: *) = SimplifyM
  { runSimplifyM'
    :: SubstReaderT AtomSubstVal (DoubleBuilderT SimpIR TopEnvFrag  HardFailM) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader AtomSubstVal, MonadFail
           , Builder SimpIR, HoistingTopBuilder TopEnvFrag)

liftSimplifyM
  :: (SinkableE e, RenameE e, TopBuilder m, Mut n)
  => (forall l. DExt n l => SimplifyM n l (e l))
  -> m n (e n)
liftSimplifyM cont = do
  Abs envFrag e <- liftM runHardFail $
    liftDoubleBuilderT $ runSubstReaderT (sink idSubst) $ runSimplifyM' cont
  emitEnv $ Abs envFrag e
{-# INLINE liftSimplifyM #-}

liftDoubleBuilderToSimplifyM :: DoubleBuilder SimpIR o a -> SimplifyM i o a
liftDoubleBuilderToSimplifyM cont = SimplifyM $ liftSubstReaderT cont

instance Simplifier SimplifyM

-- TODO: figure out why we can't derive this one (here and elsewhere)
instance ScopableBuilder SimpIR (SimplifyM i) where
  buildScoped cont = SimplifyM $ SubstReaderT $ ReaderT \env ->
    buildScoped $ runSubstReaderT (sink env) (runSimplifyM' cont)
  {-# INLINE buildScoped #-}

-- === Top-level API ===

data SimplifiedBlock n = SimplifiedBlock (SBlock n) (ReconstructAtom n)

-- TODO: extend this to work on functions instead of blocks (with blocks still
-- accessible as nullary functions)
simplifyTopBlock :: (TopBuilder m, Mut n) => Block CoreIR n -> m n (SimplifiedBlock n)
simplifyTopBlock block = liftSimplifyM $ buildSimplifiedBlock $ simplifyBlock block
{-# SCC simplifyTopBlock #-}

simplifyTopFunction :: (TopBuilder m, Mut n) => LamExpr CoreIR n -> m n (LamExpr SimpIR n)
simplifyTopFunction f = liftSimplifyM do
  (lam, CoerceReconAbs) <- simplifyLam f
  return lam
{-# SCC simplifyTopFunction #-}

applyReconTop :: (EnvReader m, Fallible1 m) => ReconstructAtom n -> SAtom n -> m n (CAtom n)
applyReconTop = applyRecon

instance GenericE SimplifiedBlock where
  type RepE SimplifiedBlock = PairE SBlock ReconstructAtom
  fromE (SimplifiedBlock block recon) = PairE block recon
  {-# INLINE fromE #-}
  toE   (PairE block recon) = SimplifiedBlock block recon
  {-# INLINE toE #-}

instance SinkableE SimplifiedBlock
instance RenameE SimplifiedBlock
instance HoistableE SimplifiedBlock
instance CheckableE SimplifiedBlock where
  checkE (SimplifiedBlock block recon) =
    -- TODO: CheckableE instance for the recon too
    SimplifiedBlock <$> checkE block <*> renameM recon

instance Pretty (SimplifiedBlock n) where
  pretty (SimplifiedBlock block recon) =
    pretty block <> hardline <> pretty recon

-- === All the bits of IR  ===

simplifyDecls :: Emits o => Nest (Decl CoreIR) i i' -> SimplifyM i' o a -> SimplifyM i o a
simplifyDecls topDecls cont = do
  s  <- getSubst
  s' <- simpDeclsSubst s topDecls
  withSubst s' cont
{-# INLINE simplifyDecls #-}

simpDeclsSubst
  :: Emits o => Subst AtomSubstVal l o -> Nest (Decl CoreIR) l i'
  -> SimplifyM i o (Subst AtomSubstVal i' o)
simpDeclsSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    let hint = (getNameHint b)
    x <- withSubst s $ simplifyExpr hint expr
    simpDeclsSubst (s <>> (b@>SubstVal x)) rest

simplifyExpr :: Emits o => NameHint -> Expr CoreIR i -> SimplifyM i o (CAtom o)
simplifyExpr hint expr = confuseGHC >>= \_ -> case expr of
  App f xs -> do
    xs' <- mapM simplifyAtom xs
    simplifyApp hint f xs'
  TabApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f'  <- simplifyAtom f
    simplifyTabApp f' (toList xs')
  Atom x -> simplifyAtom x
  PrimOp  op  -> (inline traversePrimOp) simplifyAtom op >>= simplifyOp
  ProjMethod dict i -> bindM2 projectDictMethod (simplifyAtom dict) (pure i)
  RefOp ref eff -> do
    resultTy <- getTypeSubst expr
    ref' <- toDataAtomIgnoreRecon =<< simplifyAtom ref
    eff' <- simplifyRefOp eff
    ans <- emitExpr $ RefOp ref' eff'
    liftSimpAtom (Just resultTy) ans
  Hof hof -> simplifyHof hint hof
  RecordVariantOp op -> simplifyRecordVariantOp  =<< mapM simplifyAtom op
  TabCon ty xs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    xs' <- forM xs \x -> toDataAtomIgnoreRecon =<< simplifyAtom x
    liftSimpAtom (Just ty') =<< emitExpr (TabCon tySimp xs')
  UserEffectOp _ -> error "not implemented"
  Case scrut alts resultTy _ -> do
    -- TODO: this can fail! We need to handle the case of a non-data scrutinee!
    scrut' <- simplifyAtom scrut
    altBinderTys <- caseAltsBinderTys =<< getType scrut'
    scrutSimp <- toDataAtomIgnoreRecon scrut'
    resultTy' <- substM resultTy
    defuncCase scrutSimp resultTy' \i x -> do
      Abs b body <- return $ alts !! i
      let xCoreTy = altBinderTys !! i
      x' <- liftSimpAtom (Just $ sink xCoreTy) x
      extendSubst (b@>SubstVal x') $ simplifyBlock body

simplifyRefOp :: Emits o => RefOp CoreIR i -> SimplifyM i o (RefOp SimpIR o)
simplifyRefOp = \case
  MExtend (BaseMonoid em cb) x -> do
    em'  <- toDataAtomIgnoreRecon =<< simplifyAtom em
    x'   <- toDataAtomIgnoreRecon =<< simplifyAtom x
    (cb', CoerceReconAbs) <- simplifyLam cb
    return $ MExtend (BaseMonoid em' cb') x'
  MGet   -> return MGet
  MPut x -> MPut <$> (toDataAtomIgnoreRecon =<< simplifyAtom x)
  MAsk   -> return MAsk
  IndexRef x -> IndexRef <$> (toDataAtomIgnoreRecon =<< simplifyAtom x)
  ProjRef i -> return $ ProjRef i

caseComputingEffs
  :: forall m n r. (MonadFail1 m, EnvReader m, IRRep r)
  => Atom r n -> [Alt r n] -> Type r n -> m n (Expr r n)
caseComputingEffs scrut alts resultTy = do
  Case scrut alts resultTy <$> foldMapM getEffects alts
{-# INLINE caseComputingEffs #-}

defuncCase
  :: Emits o
  => Atom SimpIR o -> Type CoreIR o
  -> (forall o'. (Emits o', DExt o o') => Int -> SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (CAtom o)
defuncCase scrut resultTy cont = do
  case trySelectBranch scrut of
    Just (i, arg) -> getDistinct >>= \Distinct -> cont i arg
    Nothing -> do
      scrutTy <- getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      tryGetRepType resultTy >>= \case
        Just resultTyData -> do
          alts' <- forM (enumerate altBinderTys) \(i, bTy) -> do
            buildAbs noHint bTy \x -> do
              buildBlock $ cont i (sink $ Var x) >>= toDataAtomIgnoreRecon
          caseExpr <- caseComputingEffs scrut alts' resultTyData
          emitExpr caseExpr >>= liftSimpAtom (Just resultTy)
        Nothing -> do
          split <- splitDataComponents resultTy
          (alts', recons) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
             simplifyAlt split bTy $ cont i
          closureTys <- mapM getAltNonDataTy alts'
          let closureSumTy = SumTy closureTys
          let newNonDataTy = nonDataTy split
          alts'' <- forM (enumerate alts') \(i, alt) -> injectAltResult closureTys i alt
          caseExpr <- caseComputingEffs scrut alts'' (PairTy (dataTy split) closureSumTy)
          caseResult <- emitExpr $ caseExpr
          (dataVal, sumVal) <- fromPair caseResult
          reconAlts <- forM (zip closureTys recons) \(ty, recon) ->
            buildAbs noHint ty \v -> applyRecon (sink recon) (Var v)
          let nonDataVal = SimpInCore $ ACase sumVal reconAlts newNonDataTy
          Distinct <- getDistinct
          fromSplit split dataVal nonDataVal
simplifyAlt
  :: SplitDataNonData n
  -> SType o
  -> (forall o'. (Emits o', DExt o o') => SAtom o' -> SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (Alt SimpIR o, ReconstructAtom o)
simplifyAlt split ty cont = fromPairE <$> do
  withFreshBinder noHint ty \b -> do
    ab <- buildScoped $ cont $ sink $ Var $ binderName b
    (resultWithDecls, recon) <- refreshAbs ab \decls result -> do
      let locals = toScopeFrag b >>> toScopeFrag decls
      -- TODO: this might be too cautious. The type only needs to
      -- be hoistable above the decls. In principle it can still
      -- mention vars from the lambda binders.
      Distinct <- getDistinct
      (resultData, resultNonData) <- toSplit split result
      (newResult, reconAbs) <- telescopicCapture locals resultNonData
      return (Abs decls (PairVal resultData newResult), LamRecon reconAbs)
    block <- makeBlockFromDecls resultWithDecls
    return $ PairE (Abs (b:>ty) block) recon

getAltNonDataTy :: EnvReader m => Alt SimpIR n -> m n (SType n)
getAltNonDataTy (Abs bs body) = liftSubstEnvReaderM do
  substBinders bs \bs' -> do
    ~(PairTy _ ty) <- getTypeSubst body
    -- Result types of simplified abs should be hoistable past binder
    return $ ignoreHoistFailure $ hoist bs' ty

simplifyPossiblyNullaryApp :: forall i o. Emits o
  => NameHint -> CAtom i -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyPossiblyNullaryApp hint f xs = case NE.nonEmpty xs of
  Nothing -> substM f
  Just xs' -> simplifyApp hint f xs'

simplifyApp :: forall i o. Emits o
  => NameHint -> CAtom i -> NE.NonEmpty (CAtom o) -> SimplifyM i o (CAtom o)
simplifyApp hint f xs =  case f of
  Lam lam arr eff -> fast lam arr eff
  _ -> slow =<< simplifyAtomAndInline f
  where
    fast :: LamExpr CoreIR i' -> Arrow -> EffAbs i' -> SimplifyM i' o (CAtom o)
    fast lam arr eff = case fromNaryLam (NE.length xs) (Lam lam arr eff) of
      Just (bsCount, LamExpr bs (Block _ decls atom)) -> do
          let (xsPref, xsRest) = NE.splitAt bsCount xs
          extendSubst (bs@@>(SubstVal <$> xsPref)) $ simplifyDecls decls $
            case NE.nonEmpty xsRest of
              Nothing    -> simplifyAtom atom
              Just rest' -> simplifyApp hint atom rest'
      Nothing -> error "should never happen"

    slow :: CAtom o -> SimplifyM i o (CAtom o)
    slow atom = case atom of
      Lam lam arr eff -> dropSubst $ fast lam arr eff
      SimpInCore (ACase e alts ty) -> dropSubst do
        resultTy <- getAppType ty (toList xs)
        defuncCase e resultTy \i x -> do
          Abs b body <- return $ alts !! i
          extendSubst (b@>SubstVal x) do
            xs' <- mapM sinkM xs
            simplifyApp hint body xs'
      SimpInCore (LiftSimpFun (PiType b _ resultTy) (LamExpr bs body)) -> do
        if nestLength bs /= length xs
          then error "Expect saturated application, right?"
          else do
            let resultTy' = ignoreHoistFailure $ hoist b resultTy
            xs' <- mapM toDataAtomIgnoreRecon $ toList xs
            body' <- applySubst (bs@@>map SubstVal xs') body
            liftSimpAtom (Just resultTy') =<< emitBlock body'
      Var v -> do
        lookupAtomName v >>= \case
          NoinlineFun noInlineDef -> simplifyTopFunApp v noInlineDef (toList xs)
          FFIFunBound _ f' -> do
            xs' <- mapM toDataAtomIgnoreRecon $ toList xs
            liftSimpAtom Nothing =<< naryTopApp f' xs'
          b -> error $ "Should only have noinline functions left " ++ pprint b
      _ -> error $ "Unexpected function: " ++ pprint atom

-- | Like `simplifyAtom`, but will try to inline function definitions found
-- in the environment. The only exception is when we're going to differentiate
-- and the function has a custom derivative rule defined.
-- TODO(dougalm): do we still need this?
simplifyAtomAndInline :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtomAndInline atom = confuseGHC >>= \_ -> case atom of
  Var v -> do
    env <- getSubst
    case env ! v of
      Rename v' -> doInline v'
      SubstVal (Var v') -> doInline v'
      SubstVal x -> return x
  _ -> simplifyAtom atom >>= \case
    Var v -> doInline v
    ans -> return ans
  where
    doInline v = do
      lookupAtomName v >>= \case
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtomAndInline x
        _ -> return $ Var v

simplifyTopFunApp :: Emits n => CAtomName n -> NoInlineDef n -> [CAtom n] -> SimplifyM i n (CAtom n)
simplifyTopFunApp v def xs = do
  NoInlineDef numSpecializationArgs _ piTy _ _ <- return def
  withSaturatingArgs piTy xs \xs' -> do
    case splitAtExact numSpecializationArgs (toList xs') of
      Just (specializationArgs, runtimeArgs) -> do
        (spec, extraArgs) <- determineSpecializationSpec (sink v) specializationArgs
        ab <- getSpecializedFunction spec
        Just specializedFunction <- emitHoistedEnv ab
        allArgs <- mapM toDataAtomIgnoreRecon (extraArgs ++ runtimeArgs)
        naryTopApp specializedFunction allArgs
      Nothing -> error $ "Specialization of " ++ pprint v ++
        " requires saturated application of specialization args."

-- supplies enough args to saturate application, eta-expanding as needed
withSaturatingArgs
  :: Emits n => NaryPiType CoreIR n -> [CAtom n]
  -> (forall l. (Emits l, DExt n l) => [CAtom l] -> SimplifyM i l (SAtom l))
  -> SimplifyM i n (CAtom n)
withSaturatingArgs piTy xs contTop = do
  piTy'@(NaryPiType bsRest _ resultTy) <- instantiateNaryPi piTy xs
  case bsRest of
    Empty -> do
      Distinct <- getDistinct
      liftSimpAtom (Just resultTy) =<< contTop xs
    _ -> do
      lam <- go bsRest \xsRest -> contTop $ sinkList xs ++ xsRest
      liftSimpFun (naryPiTypeAsType piTy') lam
  where
    go :: Nest CBinder n any
       -> (forall l. (Emits l, DExt n l) => [CAtom l] -> SimplifyM i l (SAtom l))
       -> SimplifyM i n (SLam n)
    go Empty cont = do
      block <- buildBlock $ cont []
      return $ LamExpr Empty block
    go (Nest (b:>cTy) bs) cont = do
      sTy <- getRepType cTy
      withFreshBinder (getNameHint b) sTy \b' -> do
        x' <- liftSimpAtom (Just $ sink cTy) (Var $ binderName b')
        Abs bs' UnitE <- applySubst (b@>SubstVal x') (Abs bs UnitE)
        LamExpr bs'' body <- go bs' \xs' -> cont $ sink x' : xs'
        return $ LamExpr (Nest (b':>sTy) bs'') body

determineSpecializationSpec
  :: EnvReader m => AtomName CoreIR n -> [CAtom n] -> m n (SpecializationSpec n, [CAtom n])
determineSpecializationSpec fname staticArgs = do
  lookupAtomName fname >>= \case
    NoinlineFun (NoInlineDef _ arrs (NaryPiType bs _ _) _ _) -> do
      (PairB staticArgBinders _) <- return $ splitNestAt (length staticArgs) bs
      let staticArrs = take (length staticArgs) arrs
      (ab, extraArgs) <- generalizeArgs staticArrs staticArgBinders staticArgs
      return (AppSpecialization fname ab, extraArgs)
    _ -> error "should only be specializing top functions"

getSpecializedFunction :: EnvReader m => SpecializationSpec n -> m n (Abs TopEnvFrag TopFunName n)
getSpecializedFunction s = do
  querySpecializationCache s >>= \case
    Just name -> return $ Abs emptyOutFrag name
    _ -> liftTopBuilderHoisted $ emitSpecialization (sink s)

emitSpecialization :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (TopFunName n)
emitSpecialization s = do
  let hint = getNameHint s
  fCore <- specializedFunCoreDefinition s
  fSimp <- simplifyTopFunction fCore
  name <- emitTopFunBinding hint (Specialization s) fSimp
  extendSpecializationCache s name
  return name

specializedFunCoreDefinition :: (Mut n, TopBuilder m) => SpecializationSpec n -> m n (LamExpr CoreIR n)
specializedFunCoreDefinition s@(AppSpecialization f (Abs bs staticArgs)) = do
  ty <- specializedFunCoreTypeTop s
  liftBuilder $ buildNaryLamExprFromPi ty \allArgs -> do
    -- This is needed to avoid an infinite loop. Otherwise, in simplifyTopFunction,
    -- where we eta-expand and try to simplify `App f args`, we would see `f` as a
    -- "noinline" function and defer its simplification.
    NoinlineFun (NoInlineDef _ _ _ _ f') <- lookupAtomName (sink f)
    let (extraArgs, originalArgs) = splitAt (nestLength bs) (toList allArgs)
    ListE staticArgs' <- applyRename (bs@@>extraArgs) staticArgs
    naryApp (sink f') $ staticArgs' <> map Var originalArgs

specializedFunCoreTypeTop
  :: (Mut n, TopBuilder m)
  => SpecializationSpec n -> m n (NaryPiType CoreIR n)
specializedFunCoreTypeTop spec = liftSimplifyM $ specializedFunCoreType $ sink spec

specializedFunCoreType :: SpecializationSpec n -> SimplifyM i n (NaryPiType CoreIR n)
specializedFunCoreType (AppSpecialization f ab) = do
  refreshAbs ab \extraArgBs (ListE staticArgs) -> do
    lookupAtomName (sink f) >>= \case
      NoinlineFun (NoInlineDef _ _ fTy _ _) -> do
        NaryPiType dynArgBs effs resultTy <- instantiateNaryPi fTy staticArgs
        let allBs = extraArgBs >>> dynArgBs
        return $ NaryPiType allBs effs resultTy
      _ -> error "should only be specializing top-level functions"

simplifyTabApp :: forall i o. Emits o
  => CAtom o -> [CAtom o] -> SimplifyM i o (CAtom o)
simplifyTabApp f [] = return f
simplifyTabApp f@(SimpInCore sic) xs = case sic of
  TabLam _ _ -> do
    case fromNaryTabLam (length xs) f of
      Just (bsCount, Abs bs declsAtom) -> do
        let (xsPref, xsRest) = splitAt bsCount xs
        xsPref' <- mapM toDataAtomIgnoreRecon xsPref
        Abs decls atom <- applySubst (bs@@>(SubstVal <$> xsPref')) declsAtom
        atom' <- emitDecls decls atom
        simplifyTabApp atom' xsRest
      Nothing -> error "should never happen"
  ACase e alts ty -> dropSubst do
    resultTy <- getTabAppType ty (toList xs)
    defuncCase e resultTy \i x -> do
      Abs b body <- return $ alts !! i
      extendSubst (b@>SubstVal x) do
        xs' <- mapM sinkM xs
        body' <- substM body
        simplifyTabApp body' xs'
  LiftSimp _ f' -> do
    fTy <- getType f
    resultTy <- getTabAppType fTy xs
    xs' <- mapM toDataAtomIgnoreRecon xs
    liftSimpAtom (Just resultTy) =<< naryTabApp f' xs'
  LiftSimpFun _ _ -> error "not implemented"
simplifyTabApp f _ = error $ "Unexpected table: " ++ pprint f

simplifyIxType :: IxType CoreIR o -> SimplifyM i o (IxType SimpIR o)
simplifyIxType (IxType t ixDict) = do
  t' <- getRepType t
  IxType t' <$> case ixDict of
    IxDictAtom (DictCon (IxFin n)) -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'
    IxDictAtom d -> do
      (dictAbs, params) <- generalizeIxDict =<< cheapNormalize d
      params' <- mapM toDataAtomIgnoreReconAssumeNoDecls params
      sdName <- requireIxDictCache dictAbs
      return $ IxDictSpecialized t' sdName params'
    -- TODO: remove these two coercions once we disallow these cases in CoreIR
    IxDictRawFin n            -> do
      n' <- toDataAtomIgnoreReconAssumeNoDecls n
      return $ IxDictRawFin n'
    IxDictSpecialized ty d xs ->
      return $ unsafeCoerceIRE $ IxDictSpecialized ty d xs

requireIxDictCache
  :: (HoistingTopBuilder TopEnvFrag m) => AbsDict n -> m n (Name SpecializedDictNameC n)
requireIxDictCache dictAbs = do
  queryIxDictCache dictAbs >>= \case
    Just name -> return name
    Nothing -> do
      ab <- liftTopBuilderHoisted do
        dName <- emitBinding "d" $ sink $ SpecializedDictBinding $ SpecializedDict dictAbs Nothing
        extendCache $ mempty { ixDictCache = eMapSingleton (sink dictAbs) dName }
        return dName
      maybeD <- emitHoistedEnv ab
      case maybeD of
        Just name -> return name
        Nothing -> error "Couldn't hoist specialized dictionary"
{-# INLINE requireIxDictCache #-}

-- TODO: do we even need this, or is it just a glorified `SubstM`?
simplifyAtom :: CAtom i -> SimplifyM i o (CAtom o)
simplifyAtom atom = confuseGHC >>= \_ -> case atom of
  Var v -> simplifyVar v
  Lam _ _ _  -> substM atom
  Pi _ -> substM atom
  TabPi _ -> substM atom
  DepPairTy _ -> substM atom
  DepPair x y ty -> DepPair <$> simplifyAtom x <*> simplifyAtom y <*> substM ty
  Con con -> Con <$> (inline traversePrimCon) simplifyAtom con
  TC tc -> TC <$> (inline traversePrimTC) simplifyAtom tc
  Eff eff -> Eff <$> substM eff
  PtrVar v -> PtrVar <$> substM v
  DictCon d -> (DictCon <$> substM d) >>= cheapNormalize
  DictTy  d -> DictTy <$> substM d
  NewtypeCon _ _ -> substM atom
  NewtypeTyCon t -> NewtypeTyCon <$> substM t
  ProjectElt i x -> normalizeProj i =<< simplifyAtom x
  SimpInCore _ -> substM atom

simplifyVar :: AtomName CoreIR i -> SimplifyM i o (CAtom o)
simplifyVar v = do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      AtomNameBinding bindingInfo <- lookupEnv v'
      case bindingInfo of
        -- Functions get inlined only at application sites
        LetBound (DeclBinding _ (Pi _) _) -> return $ Var v'
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ simplifyAtom x
        _ -> return $ Var v'

-- Assumes first order (args/results are "data", allowing newtypes), monormophic
simplifyLam
  :: LamExpr CoreIR i
  -> SimplifyM i o (LamExpr SimpIR o, Abs (Nest (AtomNameBinder SimpIR)) ReconstructAtom o)
simplifyLam (LamExpr bsTop body) = case bsTop of
  Nest (b:>ty) bs -> do
    ty' <- substM ty
    tySimp <- getRepType ty'
    withFreshBinder (getNameHint b) tySimp \b' -> do
      x <- liftSimpAtom (Just $ sink ty') (Var $ binderName b')
      extendSubst (b@>SubstVal x) do
        (LamExpr bs' body', Abs bsRecon recon) <- simplifyLam $ LamExpr bs body
        return (LamExpr (Nest (b':>tySimp) bs') body', Abs (Nest b' bsRecon) recon)
  Empty -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    return (LamExpr Empty body', Abs Empty recon)

data SplitDataNonData n = SplitDataNonData
  { dataTy    :: Type SimpIR n
  , nonDataTy :: Type CoreIR n
  , toSplit   :: forall i l . CAtom l -> SimplifyM i l (SAtom l, CAtom l)
  , fromSplit :: forall i l . DExt n l => SAtom l -> CAtom l -> SimplifyM i l (CAtom l) }

-- bijection between that type and a (data, non-data) pair type.
splitDataComponents :: Type CoreIR n -> SimplifyM i n (SplitDataNonData n)
splitDataComponents = \case
  ProdTy tys -> do
    splits <- mapM splitDataComponents tys
    return $ SplitDataNonData
      { dataTy    = ProdTy $ map dataTy    splits
      , nonDataTy = ProdTy $ map nonDataTy splits
      , toSplit = \xProd -> do
          xs <- getUnpacked xProd
          (ys, zs) <- unzip <$> forM (zip xs splits) \(x, split) -> toSplit split x
          return (ProdVal ys, ProdVal zs)
      , fromSplit = \xsProd ysProd -> do
          xs <- getUnpacked xsProd
          ys <- getUnpacked ysProd
          zs <- forM (zip (zip xs ys) splits) \((x, y), split) -> fromSplit split x y
          return $ ProdVal zs }
  ty -> tryGetRepType ty >>= \case
    Just repTy -> return $ SplitDataNonData
      { dataTy = repTy
      , nonDataTy = UnitTy
      , toSplit = \x -> (,UnitVal) <$> toDataAtomIgnoreReconAssumeNoDecls x
      , fromSplit = \x _ -> liftSimpAtom (Just $ sink ty) x }
    Nothing -> return $ SplitDataNonData
      { dataTy = UnitTy
      , nonDataTy = ty
      , toSplit = \x -> return (UnitVal, x)
      , fromSplit = \_ x -> return x }

buildSimplifiedBlock
  :: (forall o'. (Emits o', DExt o o') => SimplifyM i o' (CAtom o'))
  -> SimplifyM i o (SimplifiedBlock o)
buildSimplifiedBlock cont = do
  Abs decls eitherResult <- buildScoped do
    ans <- cont
    tryAsDataAtom ans >>= \case
      Nothing -> return $ LeftE ans
      Just (dataResult, _) -> do
        ansTy <- getType ans
        return $ RightE (dataResult `PairE` ansTy)
  case eitherResult of
    LeftE ans -> do
      (declsResult, recon) <- refreshAbs (Abs decls ans) \decls' ans' -> do
        (newResult, reconAbs) <- telescopicCapture (toScopeFrag decls') ans'
        return (Abs decls' newResult, LamRecon reconAbs)
      block <- makeBlockFromDecls declsResult
      return $ SimplifiedBlock block recon
    RightE (ans `PairE` ty) -> do
      block <- makeBlockFromDecls $ Abs decls ans
      let ty' = ignoreHoistFailure $ hoist (toScopeFrag decls) ty
      return $ SimplifiedBlock block (CoerceRecon ty')

simplifyRecordVariantOp :: Emits o => RecordVariantOp (CAtom o) -> SimplifyM i o (CAtom o)
simplifyRecordVariantOp op = case op of
  RecordCons left right -> getType left >>= \case
    StaticRecordTy leftTys -> getType right >>= \case
      StaticRecordTy rightTys -> do
        -- Unpack, then repack with new arguments (possibly in the middle).
        leftList <- getUnpacked $ unwrapNewtype left
        let leftItems = restructure leftList leftTys
        rightList <- getUnpacked $ unwrapNewtype right
        let rightItems = restructure rightList rightTys
        return $ Record (void (leftTys <> rightTys)) $ toList $ leftItems <> rightItems
      _ -> error "not a record"
    _ -> error "not a record"
  RecordConsDynamic ~(NewtypeTyCon (LabelCon l)) val rec -> do
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked $ unwrapNewtype rec
        let items = restructure itemList itemTys
        return $ Record (labeledSingleton l () <> void itemTys) $
          toList $ labeledSingleton l val <> items
      _ -> error "not a record"
  RecordSplit f full -> getType full >>= \case
    StaticRecordTy fullTys -> case f of
      LabeledRow f' | [StaticFields fields] <- fromFieldRowElems f' -> do
        -- Unpack, then repack into two pieces.
        fullList <- getUnpacked $ unwrapNewtype full
        let fullItems = restructure fullList fullTys
        let (_, remaining) = splitLabeledItems fields fullTys
        let (left, right) = splitLabeledItems fields fullItems
        return $ PairVal (Record (void fields)    (toList left ))
                         (Record (void remaining) (toList right))
      _ -> error "failed to simplifiy a field row"
    _ -> error "not a record"
  RecordSplitDynamic ~(NewtypeTyCon (LabelCon l)) rec ->
    getType rec >>= \case
      StaticRecordTy itemTys -> do
        itemList <- getUnpacked $ unwrapNewtype rec
        let items = restructure itemList itemTys
        let (val, rest) = splitLabeledItems (labeledSingleton l ()) items
        let (_, otherItemTys) = splitLabeledItems (labeledSingleton l ()) itemTys
        return $ PairVal (head $ toList val) $
          Record (void otherItemTys) $ toList rest
      _ -> error "not a record"
  VariantLift leftTys right -> do
    VariantTy (NoExt rightTys) <- getType right
    let fullTys = leftTys <> rightTys
    let fullLabels = toList $ reflectLabels fullTys
    let labels = toList $ reflectLabels rightTys
    -- Emit a case statement (ordered by the arg type) that lifts the type.
    rightSimp <- toDataAtomIgnoreRecon right
    resTy <- getResTy
    resTySimp <- getRepType resTy
    liftSimpAtom (Just resTy) =<< buildCase rightSimp resTySimp \caseIdx v -> do
      -- TODO: This is slow! Optimize this! We keep searching through lists all the time!
      let (label, i) = labels !! caseIdx
      let idx = fromJust $ elemIndex (label, i + length (lookupLabel leftTys label)) fullLabels
      SumTy resTys <- sinkM resTySimp
      return $ SumVal resTys idx v
  VariantSplit leftTysLabeled full' -> do
    VariantTy (NoExt fullTysLabeled) <- getType full'
    let rightTysLabeled = snd $ splitLabeledItems leftTysLabeled fullTysLabeled
    resTy <- getResTy
    leftTys <- forM (toList leftTysLabeled) \t -> getRepType t
    rightTys <- mapM getRepType $ toList rightTysLabeled
    full <- toDataAtomIgnoreRecon full'
    resTySimp <- getRepType resTy
    liftSimpAtom (Just resTy) =<< buildCase full resTySimp \caseIdx v -> do
      SumTy resTys <- sinkM resTySimp
      let (label, i) = toList (reflectLabels fullTysLabeled) !! caseIdx
      let labelIx labs li = fromJust $ elemIndex li (toList $ reflectLabels labs)
      case leftTysLabeled `lookupLabel` label of
        [] -> return $ SumVal resTys 1 $ SumVal (sinkList rightTys) (labelIx rightTysLabeled (label, i)) v
        tys -> if i < length tys
          then return $ SumVal resTys 0 $ SumVal (sinkList leftTys ) (labelIx leftTysLabeled (label, i)) v
          else return $ SumVal resTys 1 $ SumVal (sinkList rightTys) (labelIx rightTysLabeled (label, i - length tys)) v
  VariantMake ~(VariantTy (NoExt tys)) label i v -> do
    let ix = fromJust $ elemIndex (label, i) $ toList $ reflectLabels tys
    return $ NewtypeCon (VariantCon (void tys)) $ SumVal (toList tys) ix v
  SumToVariant c -> do
    SumTy cases <- getType c
    let labels = foldMap (const $ labeledSingleton "c" ()) cases
    return $ NewtypeCon (VariantCon labels) c
  where
    getResTy = getType (RecordVariantOp op)

simplifyOp :: Emits o => PrimOp (CAtom o) -> SimplifyM i o (CAtom o)
simplifyOp op = do
  ty <- getType $ PrimOp op
  case op of
    BinOp binop x' y' -> do
      x <- toDataAtomIgnoreRecon x'
      y <- toDataAtomIgnoreRecon y'
      liftSimpAtom (Just ty) =<< case binop of
        ISub -> isub x y
        IAdd -> iadd x y
        IMul -> imul x y
        IDiv -> idiv x y
        ICmp Less  -> ilt x y
        ICmp Equal -> ieq x y
        _ -> fallback
    MiscOp (Select c' x' y') -> do
      c <- toDataAtomIgnoreRecon c'
      x <- toDataAtomIgnoreRecon x'
      y <- toDataAtomIgnoreRecon y'
      liftSimpAtom (Just ty) =<< select c x y
    MiscOp (ShowAny x) -> dropSubst $ showAny x >>= simplifyBlock
    _ -> liftSimpAtom (Just ty) =<< fallback
    where
      fallback = do
        op' <- (inline traversePrimOp) toDataOrRepType op
        liftEnvReaderM (peepholeOp op') >>= \case
          Left  a   -> return a
          Right op'' -> emitOp op''

pattern CoerceReconAbs :: Abs (Nest b) ReconstructAtom n
pattern CoerceReconAbs <- Abs _ (CoerceRecon _)

projectDictMethod :: Emits o => CAtom o -> Int -> SimplifyM i o (CAtom o)
projectDictMethod d i = do
  cheapNormalize d >>= \case
    DictCon (InstanceDict instanceName args) -> dropSubst do
      args' <- mapM simplifyAtom args
      InstanceDef _ bs _ body <- lookupInstanceDef instanceName
      let InstanceBody _ methods = body
      let method = methods !! i
      extendSubst (bs@@>(SubstVal <$> args')) $
        simplifyBlock method
    DictCon (IxFin n) -> projectIxFinMethod (toEnum i) n
    d' -> error $ "Not a simplified dict: " ++ pprint d'

simplifyHof :: Emits o => NameHint -> Hof CoreIR i -> SimplifyM i o (CAtom o)
simplifyHof _hint hof = case hof of
  For d ixDict lam -> do
    (lam', Abs (UnaryNest bIx) recon) <- simplifyLam lam
    ixTypeCore <- ixTyFromDict =<< substM ixDict
    ixTypeSimp@(IxType _ ixDict') <- simplifyIxType ixTypeCore
    ans <- emitExpr $ Hof $ For d ixDict' lam'
    case recon of
      CoerceRecon _ -> do
        resultTy <- getTypeSubst $ Hof hof
        liftSimpAtom (Just resultTy) ans
      LamRecon (Abs bsClosure reconResult) -> do
        TabPi resultTy <- getTypeSubst $ Hof hof
        liftM (SimpInCore . TabLam resultTy) $
          buildAbs noHint ixTypeSimp \i -> buildScoped do
            i' <- sinkM i
            xs <- unpackTelescope =<< tabApp (sink ans) (Var i')
            applySubst (bIx@>Rename i' <.> bsClosure @@> map SubstVal xs) reconResult
  While body -> do
    SimplifiedBlock body' (CoerceRecon resultTy) <- buildSimplifiedBlock $ simplifyBlock body
    result <- emitExpr (Hof $ While body')
    liftSimpAtom (Just resultTy) result
  RunReader r lam -> do
    r' <- toDataAtomIgnoreRecon =<< simplifyAtom r
    (lam', Abs b recon) <- simplifyLam lam
    ans <- emitExpr $ Hof $ RunReader r' lam'
    let recon' = ignoreHoistFailure $ hoist b recon
    applyRecon recon' ans
  RunWriter Nothing (BaseMonoid e combine) lam -> do
    (e', wTy) <- toDataAtom =<< simplifyAtom e
    (combine', CoerceReconAbs) <- simplifyLam combine
    (lam', Abs b recon) <- simplifyLam lam
    let hof' = Hof $ RunWriter Nothing (BaseMonoid e' combine') lam'
    (ans, w) <- fromPair =<< emitExpr hof'
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    w' <- liftSimpAtom wTy w
    return $ PairVal ans' w'
  RunWriter _ _ _ -> error "Shouldn't see a RunWriter with a dest in Simplify"
  RunState Nothing s lam -> do
    (s', sTy) <- toDataAtom =<< simplifyAtom s
    (lam', Abs b recon) <- simplifyLam lam
    resultPair <- emitExpr $ Hof $ RunState Nothing s' lam'
    (ans, sOut) <- fromPair resultPair
    let recon' = ignoreHoistFailure $ hoist b recon
    ans' <- applyRecon recon' ans
    sOut' <- liftSimpAtom sTy sOut
    return $ PairVal ans' sOut'
  RunState _ _ _ -> error "Shouldn't see a RunState with a dest in Simplify"
  RunIO body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitExpr $ Hof $ RunIO body'
    applyRecon recon ans
  RunInit body -> do
    SimplifiedBlock body' recon <- buildSimplifiedBlock $ simplifyBlock body
    ans <- emitExpr $ Hof $ RunInit body'
    applyRecon recon ans
  Linearize lam x -> do
    x' <- toDataAtomIgnoreRecon =<< simplifyAtom x
    -- XXX: we're ignoring the result type here, which only makes sense if we're
    -- dealing with functions on simple types.
    (lam', recon) <- simplifyLam lam
    CoerceReconAbs <- return recon
    (result, linFun) <- liftDoubleBuilderToSimplifyM $ linearize lam' x'
    PairTy resultTy linFunTy <- getTypeSubst $ Hof hof
    result' <- liftSimpAtom (Just resultTy) result
    linFun' <- liftSimpFun linFunTy linFun
    return $ PairVal result' linFun'
  Transpose lam x -> do
    (lam', CoerceReconAbs) <- simplifyLam lam
    x' <- toDataAtomIgnoreRecon =<< simplifyAtom x
    result <- transpose lam' x'
    resultTy <- getTypeSubst $ Hof hof
    liftSimpAtom (Just resultTy) result
  CatchException body-> do
    SimplifiedBlock body' (CoerceRecon ty) <- buildSimplifiedBlock $ simplifyBlock body
    block <- liftBuilder $ runSubstReaderT idSubst $
      buildBlock $ exceptToMaybeBlock $ body'
    result <- emitBlock block
    liftSimpAtom (Just ty) result

simplifyBlock :: Emits o => Block CoreIR i -> SimplifyM i o (CAtom o)
simplifyBlock (Block _ decls result) = simplifyDecls decls $ simplifyAtom result

-- === simplifying custom linearizations ===

linearizeTopFun :: (Mut n, Fallible1 m, TopBuilder m) => LinearizationSpec n -> m n (TopFunName n, TopFunName n)
linearizeTopFun spec = do
  -- TODO: package up this caching pattern so we don't keep reimplementing it
  queryLinearizationCache spec >>= \case
    Just (primal, tangent) -> return (primal, tangent)
    Nothing -> do
      (primal, tangent) <- linearizeTopFunNoCache spec
      extendLinearizationCache spec (primal, tangent)
      return (primal, tangent)

linearizeTopFunNoCache :: (Mut n, TopBuilder m) => LinearizationSpec n -> m n (TopFunName n, TopFunName n)
linearizeTopFunNoCache spec@(LinearizationSpec f actives) = lookupEnv f >>= \case
  TopFunBinding (DexTopFun (Specialization (AppSpecialization fCore absParams)) _ _ _) -> do
    lookupCustomRules fCore >>= \case
      Just customRule -> do
        PairE fPrimal fTangent <- liftSimplifyM $
          simplifyCustomLinearization (sink absParams) actives (sink customRule)
        (,) <$> emitTopFunBinding "primal"  (LinearizationPrimal  spec) fPrimal
            <*> emitTopFunBinding "tangent" (LinearizationTangent spec) fTangent
      Nothing -> error "not implemented" -- TODO: if there's no custom rule, derive it from the
  b -> error $ "not implemented: " ++ pprint b


type Linearized = Abs (Nest SBinder)    -- primal args
                      (Abs (Nest SDecl) -- primal decls
                      (PairE SAtom      -- primal result
                             SLam))     -- tangent function

simplifyCustomLinearization
  :: Abstracted CoreIR (ListE CType) n -> [Active] -> AtomRules n
  -> SimplifyM i n (PairE SLam SLam n)
simplifyCustomLinearization (Abs genBs params) actives rule = do
  let actives' = drop (nestLength genBs) actives
  CustomLinearize nImplicit nExplicit zeros fCustom <- return rule
  defuncLinearized =<< withSimplifiedBinders genBs \genBs' genArgs -> do
    ListE params' <- applySubst (genBs @@> (SubstVal <$> genArgs)) params
    Just customRuleTy <- fromNaryPiType (nImplicit + nExplicit) <$> getType (sink fCustom)
    NaryPiType primalBs _ _ <- instantiateNaryPi customRuleTy params'
    withSimplifiedBinders primalBs \primalBs' primalArgs -> do
      ListE params'' <- sinkM $ ListE params'
      let allArgs = params'' ++ primalArgs
      scoped <- buildScoped do
        fCustom' <- sinkM fCustom
        pairResult <- dropSubst $ simplifyPossiblyNullaryApp noHint fCustom' (sinkList allArgs)
        (primalResult, fLin) <- fromPair pairResult
        primalResult' <- toDataAtomIgnoreRecon primalResult
        allTangentTys <- forM (sinkList primalArgs) \primalArg -> do
          tangentType =<< getRepType =<< getType primalArg
        activeTangentTys <- catMaybes <$> forM (zip allTangentTys actives')
          \(t, active) -> return case active of True  -> Just t; False -> Nothing
        fLin' <- buildNonDepNaryLamExpr activeTangentTys \activeTangentArgs -> do
          ListE allTangentTys' <- sinkM $ ListE allTangentTys
          tangentArgs <- buildTangentArgs zeros (zip allTangentTys' actives') (Var <$> activeTangentArgs)
          -- TODO: we're throwing away core type information here. Once we
          -- support core-level tangent types we should make an effort to
          -- correctly restore the core types before applying `fLin`. Right now,
          -- a custom linearization defined for a function on records, ADTs etc will
          -- not work.
          tangentArgs' <- mapM (liftSimpAtom Nothing) tangentArgs
          tangentResult <- dropSubst $ simplifyPossiblyNullaryApp noHint (sink fLin) tangentArgs'
          toDataAtomIgnoreRecon tangentResult
        return $ PairE primalResult' fLin'
      return $ Abs (genBs' >>> primalBs') scoped
  where
    buildTangentArgs :: Emits n => SymbolicZeros -> [(SType n, Active)] -> [SAtom n] -> SimplifyM i n [SAtom n]
    buildTangentArgs _ [] [] = return []
    buildTangentArgs zeros ((t, False):tys) activeArgs = do
      inactiveArg <- case zeros of
        SymbolicZeros -> symbolicTangentZero t
        InstantiateZeros -> zeroAt t
      rest <- buildTangentArgs zeros tys activeArgs
      return $ inactiveArg:rest
    buildTangentArgs zeros ((_, True):tys) (activeArg:activeArgs) = do
      activeArg' <- case zeros of
        SymbolicZeros -> symbolicTangentNonZero activeArg
        InstantiateZeros -> return activeArg
      rest <- buildTangentArgs zeros tys activeArgs
      return $ activeArg':rest
    buildTangentArgs _ _ _ = error "zip error"

defuncLinearized :: EnvReader m => Linearized n -> m n (PairE SLam SLam n)
defuncLinearized ab = liftBuilder $ refreshAbs ab \bs ab' -> do
  (declsAndResult, reconAbs, residualsTangentsBs) <-
    refreshAbs ab' \decls (PairE primalResult fLin) -> do
      (residuals, reconAbs) <- telescopicCapture (toScopeFrag decls) fLin
      rTy <- getType residuals
      LamExpr tBs _ <- return fLin
      residualsTangentsBs <- withFreshBinder "residual" rTy \rB -> do
        Abs tBs' UnitE <- sinkM $ Abs tBs UnitE
        return $ Abs (Nest (rB:>rTy) tBs') UnitE
      residualsTangentsBs' <- return $ ignoreHoistFailure $ hoist decls residualsTangentsBs
      return (Abs decls (PairVal primalResult residuals), reconAbs, residualsTangentsBs')
  primalFun <- LamExpr bs <$> makeBlockFromDecls declsAndResult
  LamExpr residualAndTangentBs tangentBody <- buildNaryLamExpr residualsTangentsBs \(residuals:tangents) -> do
    LamExpr tangentBs' body <- applyReconAbs (sink reconAbs) (Var residuals)
    applyRename (tangentBs' @@> tangents) body >>= emitBlock
  let tangentFun = LamExpr (bs >>> residualAndTangentBs) tangentBody
  return $ PairE primalFun tangentFun

-- === exception-handling pass ===

type HandlerM = SubstReaderT AtomSubstVal (BuilderM SimpIR)

exceptToMaybeBlock :: Emits o => SBlock i -> HandlerM i o (SAtom o)
exceptToMaybeBlock (Block (BlockAnn ty _) decls result) = do
  ty' <- substM ty
  exceptToMaybeDecls ty' decls $ Atom result
exceptToMaybeBlock (Block NoBlockAnn Empty result) = exceptToMaybeExpr $ Atom result
exceptToMaybeBlock _ = error "impossible"

exceptToMaybeDecls :: Emits o => SType o -> Nest SDecl i i' -> SExpr i' -> HandlerM i o (SAtom o)
exceptToMaybeDecls _ Empty result = exceptToMaybeExpr result
exceptToMaybeDecls resultTy (Nest (Let b (DeclBinding _ _ rhs)) decls) finalResult = do
  maybeResult <- exceptToMaybeExpr rhs
  case maybeResult of
    -- This case is just an optimization (but an important one!)
    JustAtom _ x  ->
      extendSubst (b@> SubstVal x) $ exceptToMaybeDecls resultTy decls finalResult
    _ -> emitMaybeCase maybeResult (MaybeTy resultTy)
          (return $ NothingAtom $ sink resultTy)
          (\v -> extendSubst (b@> SubstVal v) $
                   exceptToMaybeDecls (sink resultTy) decls finalResult)

exceptToMaybeExpr :: Emits o => SExpr i -> HandlerM i o (SAtom o)
exceptToMaybeExpr expr = case expr of
  Case e alts resultTy _ -> do
    e' <- substM e
    resultTy' <- substM $ MaybeTy resultTy
    buildCase e' resultTy' \i v -> do
      Abs b body <- return $ alts !! i
      extendSubst (b @> SubstVal v) $ exceptToMaybeBlock body
  Atom x -> do
    x' <- substM x
    ty <- getType x'
    return $ JustAtom ty x'
  Hof (For ann d (UnaryLamExpr b body)) -> do
    ixTy <- ixTyFromDict =<< substM d
    maybes <- buildForAnn (getNameHint b) ann ixTy \i ->
      extendSubst (b@>Rename i) $ exceptToMaybeBlock body
    catMaybesE maybes
  Hof (RunState Nothing s lam) -> do
    s' <- substM s
    BinaryLamExpr h ref body <- return lam
    result  <- emitRunState noHint s' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') do
        exceptToMaybeBlock body
    (maybeAns, newState) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
       (return $ NothingAtom $ sink a)
       (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink newState))
  Hof (RunWriter Nothing monoid (BinaryLamExpr h ref body)) -> do
    monoid' <- substM monoid
    accumTy <- substM =<< (getReferentTy $ EmptyAbs $ PairB h ref)
    result <- emitRunWriter noHint accumTy monoid' \h' ref' ->
      extendSubst (h @> Rename h' <.> ref @> Rename ref') $
        exceptToMaybeBlock body
    (maybeAns, accumResult) <- fromPair result
    a <- getTypeSubst expr
    emitMaybeCase maybeAns (MaybeTy a)
      (return $ NothingAtom $ sink a)
      (\ans -> return $ JustAtom (sink a) $ PairVal ans (sink accumResult))
  Hof (While body) -> runMaybeWhile $ exceptToMaybeBlock body
  PrimOp (MiscOp (ThrowException _)) -> do
    ty <- getTypeSubst expr
    return $ NothingAtom ty
  _ -> do
    expr' <- substM expr
    hasExceptions expr' >>= \case
      True -> error $ "Unexpected exception-throwing expression: " ++ pprint expr
      False -> do
        v <- emit expr'
        ty <- getType v
        return $ JustAtom ty (Var v)

hasExceptions :: EnvReader m => SExpr n -> m n Bool
hasExceptions expr = getEffects expr >>= \case
  EffectRow effs NoTail -> return $ ExceptionEffect `eSetMember` effs

-- === instances ===

instance GenericE ReconstructAtom where
  type RepE ReconstructAtom = EitherE2 (Type CoreIR) (ReconAbs SimpIR CAtom)

  fromE = \case
    CoerceRecon ty -> Case0 ty
    LamRecon ab    -> Case1 ab
  {-# INLINE fromE #-}
  toE = \case
    Case0 ty -> CoerceRecon ty
    Case1 ab -> LamRecon ab
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE  ReconstructAtom
instance HoistableE ReconstructAtom
instance AlphaEqE   ReconstructAtom
instance RenameE    ReconstructAtom

instance Pretty (ReconstructAtom n) where
  pretty (CoerceRecon ty) = "Coercion reconstruction: " <> pretty ty
  pretty (LamRecon ab) = "Reconstruction abs: " <> pretty ab

-- === GHC performance hacks ===

{-# SPECIALIZE
  buildNaryAbs
    :: (SinkableE e, RenameE e, SubstE (AtomSubstVal SimpIR) e, HoistableE e)
    => EmptyAbs (Nest (Binder SimpIR)) n
    -> (forall l. DExt n l => [AtomName SimpIR l] -> SimplifyM i l (e l))
    -> SimplifyM i n (Abs (Nest (Binder SimpIR)) e n) #-}

-- Note [Confuse GHC]
-- I can't explain this, but for some reason using this function in strategic
-- places makes GHC produce significantly better code. If we define
--
-- simplifyAtom = \case
--   ...
--   Con con -> traverse simplifyAtom con
--   ...
--
-- then GHC is reluctant to generate a fast-path worker function for simplifyAtom
-- that would return unboxed tuples, because (at least that's my guess) it's afraid
-- that it will have to allocate a reader closure for the traverse, which does not
-- get inlined. For some reason writing the `confuseGHC >>= \_ -> case atom of ...`
-- makes GHC do the right thing, i.e. generate unboxed worker + a tiny wrapper that
-- allocates -- a closure to be passed into traverse.
--
-- What's so special about this, I don't know. `return ()` is insufficient and doesn't
-- make the optimization go through. I'll just take the win for now...
--
-- NB: We should revise this whenever we upgrade to a newer GHC version.
confuseGHC :: SimplifyM i o (DistinctEvidence o)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
