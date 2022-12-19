-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module GenericTraversal
  ( GenericTraverser (..), GenericallyTraversableE (..)
  , GenericTraverserM (..), liftGenericTraverserM
  , traverseExprDefault, traverseAtomDefault, liftGenericTraverserMTopEmissions
  , traverseDeclNest, traverseBlock, traverseBinder ) where

import Control.Monad
import Control.Monad.State.Class

import Builder
import Core
import Err
import IRVariants
import LabeledItems
import MTL1
import Name
import Types.Core
import Types.Primitives
import Util (onSndM)

liftGenericTraverserM :: EnvReader m => s n -> GenericTraverserM r UnitB s n n a -> m n (a, s n)
liftGenericTraverserM s m =
  liftM runHardFail $ liftDoubleBuilderTNoEmissions $
    runStateT1 (runSubstReaderT idSubst $ runGenericTraverserM' m) s
{-# INLINE liftGenericTraverserM #-}

liftGenericTraverserMTopEmissions
  :: ( EnvReader m, SinkableE e, SubstE Name e, SinkableE s
     , SubstE Name s, ExtOutMap Env frag, OutFrag frag)
  => s n
  -> (forall l. DExt n l => GenericTraverserM r frag s l l (e l))
  -> m n (Abs frag (PairE e s) n)
liftGenericTraverserMTopEmissions s m =
  liftM runHardFail $ liftDoubleBuilderT do
    (e, s') <- runStateT1 (runSubstReaderT idSubst $ runGenericTraverserM' m) (sink s)
    return $ PairE e s'
{-# INLINE liftGenericTraverserMTopEmissions #-}

newtype GenericTraverserM r f s i o a =
  GenericTraverserM
    { runGenericTraverserM' :: SubstReaderT (AtomSubstVal r) (StateT1 s (DoubleBuilderT r f HardFailM)) i o a }
    deriving (Functor, Applicative, Monad, SubstReader (AtomSubstVal r), MonadFail, Fallible, MonadState (s o))

deriving instance GenericTraverser r f s => EnvExtender     (GenericTraverserM r f s i)
deriving instance GenericTraverser r f s => ScopeReader     (GenericTraverserM r f s i)
deriving instance GenericTraverser r f s => EnvReader       (GenericTraverserM r f s i)
deriving instance GenericTraverser r f s => ScopableBuilder r (GenericTraverserM r f s i)
deriving instance GenericTraverser r f s => Builder r         (GenericTraverserM r f s i)
deriving instance GenericTraverser r f s => HoistingTopBuilder f (GenericTraverserM r f s i)

class (SubstB Name f, HoistableB f, OutFrag f, ExtOutMap Env f, SinkableE s, HoistableState s)
      => GenericTraverser r f s where
  traverseExpr :: Emits o => Expr r i -> GenericTraverserM r f s i o (Expr r o)
  traverseExpr = traverseExprDefault

  traverseInlineExpr :: Emits o => Expr r i -> GenericTraverserM r f s i o (Either (Atom r o) (Expr r o))
  traverseInlineExpr e = Right <$> traverseExpr e

  traverseAtom :: Atom r i -> GenericTraverserM r f s i o (Atom r o)
  traverseAtom = traverseAtomDefault

traverseExprDefault :: Emits o => GenericTraverser r f s => Expr r i -> GenericTraverserM r f s i o (Expr r o)
traverseExprDefault expr = confuseGHC >>= \_ -> case expr of
  App g xs -> App <$> tge g <*> mapM tge xs
  TabApp g xs -> TabApp <$> tge g <*> mapM tge xs
  Atom x  -> Atom <$> tge x
  PrimOp  op -> PrimOp <$> mapM tge op
  Hof hof -> Hof  <$> tge hof
  RefOp ref eff -> RefOp <$> tge ref <*> tge eff
  Case scrut alts resultTy effs ->
    Case <$> tge scrut <*> mapM traverseAlt alts <*> tge resultTy <*> substM effs
  UserEffectOp op -> UserEffectOp <$> case op of
    Handle v xs body -> Handle <$> substM v <*> mapM tge xs <*> tge body
    Resume x y       -> Resume <$> tge x <*> tge y
    Perform x i      -> Perform <$> tge x <*> pure i
  TabCon ty xs -> TabCon <$> tge ty <*> mapM tge xs
  ProjMethod d i -> ProjMethod <$> tge d <*> pure i
  RecordVariantOp op -> RecordVariantOp <$> mapM tge op
  DAMOp op -> DAMOp <$> case op of
    Seq d ixDict carry f -> Seq d <$> tge ixDict <*> tge carry <*> tge f
    RememberDest d body  -> RememberDest <$> tge d <*> tge body
    AllocDest x          -> AllocDest <$> tge x
    Place x y            -> Place <$> tge x <*> tge y
    Freeze x             -> Freeze <$> tge x

traverseAtomDefault :: GenericTraverser r f s => Atom r i -> GenericTraverserM r f s i o (Atom r o)
traverseAtomDefault atom = confuseGHC >>= \_ -> case atom of
  Var _ -> substM atom
  Lam (UnaryLamExpr (b:>ty) body) arr effs -> do
    ty' <- tge ty
    effs' <- substM effs
    withFreshBinder (getNameHint b) (LamBinding arr ty') \b' -> do
      effs'' <- applyAbs (sink effs') (binderName b')
      extendRenamer (b@>binderName b') do
        withAllowedEffects effs'' do
          body' <- tge body
          return $ Lam (UnaryLamExpr (b':>ty') body') arr effs'
  Lam _ _ _ -> error "expected a unary lambda expression"
  Pi (PiType (PiBinder b ty arr) eff resultTy) -> do
    ty' <- tge ty
    withFreshBinder (getNameHint b) (PiBinding arr ty') \b' -> do
      extendRenamer (b@>binderName b') $
        Pi <$> (PiType (PiBinder b' ty' arr) <$> substM eff <*> tge resultTy)
  TabLam (TabLamExpr (b:>ty) body) -> do
    ty' <- tge ty
    let hint = getNameHint b
    withFreshBinder hint ty' \b' -> do
      extendRenamer (b@>binderName b') do
        body' <- tge body
        return $ TabLam $ TabLamExpr (b':>ty') body'
  TabPi (TabPiType (b:>ty) resultTy) -> do
    ty' <- tge ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendRenamer (b@>binderName b') $
        TabPi <$> (TabPiType (b':>ty') <$> tge resultTy)
  Con con -> Con <$> mapM tge con
  TC  tc  -> TC  <$> mapM tge tc
  Eff _   -> substM atom
  PtrVar _ -> substM atom
  TypeCon sn dataDefName params ->
    TypeCon sn <$> substM dataDefName <*> tge params
  DictCon dictExpr -> DictCon <$> tge dictExpr
  DictTy dictTy -> DictTy <$> tge dictTy
  LabeledRow elems -> LabeledRow <$> traverseGenericE elems
  RecordTy elems -> RecordTy <$> traverseGenericE elems
  VariantTy ext -> VariantTy <$> traverseExtLabeledItems ext
  ProjectElt _ _ -> substM atom
  DepPairTy dty -> DepPairTy <$> tge dty
  DepPair l r dty -> DepPair <$> tge l <*> tge r <*> tge dty
  RepValAtom _ -> substM atom
  -- TODO(dougalm): We don't need these because we don't use generic traversals
  -- on anything except SimpIR and CoreIR. We should add that as a constraint on
  -- `r` and then we can delete these cases.
  ACase _ _ _ -> nyi
  where nyi = error $ "not implemented: " ++ pprint atom

traverseExtLabeledItems
  :: forall r f s i o.
     GenericTraverser r f s
  => ExtLabeledItems (Atom r i) (AtomName r i)
  -> GenericTraverserM r f s i o (ExtLabeledItems (Atom r o) (AtomName r o))
traverseExtLabeledItems (Ext items rest) = do
  items' <- mapM tge items
  rest' <- flip traverse rest \r -> substM (Var r :: Atom r i) >>= \case
    Var r' -> return r'
    _ -> error "Not implemented"
  return $ Ext items' rest'

tge :: (GenericallyTraversableE r e, GenericTraverser r f s)
    => e i -> GenericTraverserM r f s i o (e o)
tge = traverseGenericE

class GenericallyTraversableE (r::IR) (e::E) | e -> r where
  traverseGenericE :: GenericTraverser r f s => e i -> GenericTraverserM r f s i o (e o)

instance GenericallyTraversableE r (Atom r) where
  traverseGenericE = traverseAtom

instance GenericallyTraversableE r (Block r) where
  traverseGenericE (Block _ decls result) = do
    buildBlock $ traverseDeclNest decls $ traverseAtom result

instance GenericallyTraversableE r (FieldRowElems r) where
  traverseGenericE elems = do
    els' <- fromFieldRowElems <$> substM elems
    dropSubst $ fieldRowElemsFromList <$> forM els' \case
      StaticFields items  -> StaticFields <$> mapM tge items
      DynField  labVar ty -> DynField labVar <$> tge ty
      DynFields rowVar    -> return $ DynFields rowVar

instance GenericallyTraversableE r (DataDefParams r) where
  traverseGenericE (DataDefParams params) =
    DataDefParams <$> mapM (onSndM tge) params

instance GenericallyTraversableE r (DepPairType r) where
  traverseGenericE (DepPairType (b:>lty) rty) = do
    lty' <- tge lty
    withFreshBinder (getNameHint b) lty' \b' -> do
      extendRenamer (b@>binderName b') $ DepPairType (b':>lty') <$> tge rty

instance GenericallyTraversableE r (BaseMonoid r) where
  traverseGenericE (BaseMonoid x f) = BaseMonoid <$> tge x <*> withAllowedEffects Pure (tge f)

instance GenericallyTraversableE r (RefOp r) where
  traverseGenericE = \case
    MGet         -> return MGet
    MPut  x      -> MPut <$> tge x
    MAsk         -> return MAsk
    MExtend bm x -> MExtend <$> tge bm <*> tge x
    IndexRef x   -> IndexRef <$> tge x
    ProjRef i    -> return $ ProjRef i

instance GenericallyTraversableE r (IxType r) where
  traverseGenericE (IxType ty dict) = IxType <$> tge ty <*> tge dict

instance GenericallyTraversableE r (DictExpr r) where
  traverseGenericE e = confuseGHC >>= \_ -> case e of
    InstanceDict v args -> InstanceDict <$> substM v <*> mapM tge args
    InstantiatedGiven given args -> InstantiatedGiven <$> tge given <*> mapM tge args
    SuperclassProj subclass i -> SuperclassProj <$> tge subclass <*> pure i
    IxFin n ->  IxFin <$> tge n
    ExplicitMethods d params -> ExplicitMethods <$> substM d <*> mapM tge params

instance GenericallyTraversableE r (DictType r) where
  traverseGenericE (DictType sn cn params) = DictType sn <$> substM cn <*> mapM tge params

instance GenericallyTraversableE r (LamExpr r) where
  traverseGenericE (LamExpr bs body) = do
    traverseBinderNest bs \bs' -> LamExpr bs' <$> tge body

instance GenericallyTraversableE r (Hof r) where
  traverseGenericE = \case
    For d ixDict f       -> For d <$> tge ixDict <*> tge f
    While body           -> While <$> tge body
    Linearize f          -> Linearize <$> tge f
    Transpose f          -> Transpose <$> tge f
    RunReader r f        -> RunReader <$> tge r <*> tge f
    RunWriter d bm f     -> RunWriter <$> mapM tge d <*> tge bm <*> tge f
    RunState d s f       -> RunState <$> mapM tge d <*> tge s <*> tge f
    RunIO body           -> RunIO <$> tge body
    RunInit body         -> RunInit <$> tge body
    CatchException body  -> CatchException <$> tge body

traverseBinderNest
  :: GenericTraverser r f s
  => Nest (Binder r) i i'
  -> (forall o'. DExt o o' => Nest (Binder r) o o' -> GenericTraverserM r f s i' o' a)
  -> GenericTraverserM r f s i o a
traverseBinderNest Empty cont = getDistinct >>= \Distinct -> cont Empty
traverseBinderNest (Nest (b:>ty) bs) cont = do
  ty' <- tge ty
  withFreshBinder (getNameHint b) ty' \b' -> do
    extendRenamer (b@>binderName b') do
      traverseBinderNest bs \bs' -> do
        cont (Nest (b':>ty') bs')

instance (GenericallyTraversableE r e1, GenericallyTraversableE r e2) =>
  (GenericallyTraversableE r (EitherE e1 e2)) where
  traverseGenericE ( LeftE e) =  LeftE <$> tge e
  traverseGenericE (RightE e) = RightE <$> tge e

traverseBlock
  :: (GenericTraverser r f s, Emits o)
  => Block r i -> GenericTraverserM r f s i o (Atom r o)
traverseBlock (Block _ decls result) = traverseDeclNest decls $ traverseAtom result

traverseDeclNest
  :: (GenericTraverser r f s, Emits o)
  => Nest (Decl r) i i'
  -> (forall o'. (Emits o', Ext o o') => GenericTraverserM r f s i' o' (e o'))
  -> GenericTraverserM r f s i o (e o)
traverseDeclNest decls cont = do
  s <- getSubst
  s' <- traverseDeclNestS s decls
  withSubst s' cont
{-# INLINE traverseDeclNest #-}

traverseDeclNestS :: (GenericTraverser r f s, Emits o)
                  => Subst (AtomSubstVal r) l o -> Nest (Decl r) l i'
                  -> GenericTraverserM r f s i o (Subst (AtomSubstVal r) i' o)
traverseDeclNestS !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    expr' <- withSubst s $ traverseInlineExpr expr
    sExt <- case expr' of
      Left a  -> return $ b @> SubstVal a
      Right e -> (b @>) . Rename <$> emitDecl (getNameHint b) ann e
    traverseDeclNestS (s <>> sExt) rest

traverseAlt
  :: GenericTraverser r f s
  => Alt r i
  -> GenericTraverserM r f s i o (Alt r o)
traverseAlt (Abs (b:>ty) body) = do
  ty' <- tge ty
  buildAbs (getNameHint b) ty' \v -> extendRenamer (b@>v) $ tge body

traverseBinder
  :: GenericTraverser r f s
  => Binder r i i'
  -> (forall o'. DExt o o' => Binder r o o' -> GenericTraverserM r f s i' o' a)
  -> GenericTraverserM r f s i o a
traverseBinder (b:>ty) cont = do
  ty' <- tge ty
  withFreshBinder (getNameHint b) ty' \b' ->
    extendRenamer (b@>binderName b') $ cont (b':>ty')

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
