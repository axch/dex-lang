-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Lower
  ( lowerFullySequential, lowerFullySequentialNoDest
  , vectorizeLoops, DestLamExpr, DestBlock
  ) where

import Prelude hiding (abs, id, (.))
import Data.Word
import Data.Functor
import Data.Maybe (fromJust)
import Data.List.NonEmpty qualified as NE
import Data.Text.Prettyprint.Doc (Pretty, pretty, viaShow, (<+>))
import Control.Category
import Control.Monad.Reader
import Control.Monad.State.Strict
import Unsafe.Coerce

import Builder
import Core
import Err
import Imp
import CheapReduction
import IRVariants
import MTL1
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Primitives
import Util (enumerate, foldMapM)

-- === For loop resolution ===

-- The `lowerFullySequential` pass makes two related changes:
-- - All `for` loops become `seq` loops
-- - Arrays are now explicily allocated as `Dest`s (whither the
--   content is written in due course)
--
-- We also perform destination passing here, to elide as many copies
-- as possible.
--
-- The idea for multithreading parallelism is to add IR elements that
-- specify parallelization strategy (`Seq` specifies sequential
-- execution) and add lowerings similar to lowerFullySequential that
-- choose which one(s) to use.

-- The `For` constructor of `PrimHof` disappears from the IR due to
-- this pass, and the `Seq`, `AllocDest`, `Place`, `RememberDest`, and
-- `Freeze` constructors appear.
--
-- All the `Place`s in the resulting IR are non-conflicting: every
-- array element is only written to once.
--
-- The traversal for a block or subexpression returns an `Atom`
-- representing the returned value.  If a destination was passed in,
-- the traversal is also responsible for arranging to write that value
-- into that destination (possibly by forwarding (a part of) the
-- destination to a sub-block or sub-expression, hence "desintation
-- passing style").

type DestLamExpr = SLam
type DestBlock = Abs (SBinder) SBlock

lowerFullySequential :: EnvReader m => SLam n -> m n (DestLamExpr n)
lowerFullySequential (LamExpr bs body) = liftEnvReaderM $ do
  refreshAbs (Abs bs body) \bs' body' -> do
    Abs b body'' <- lowerFullySequentialBlock body'
    return $ LamExpr (bs' >>> UnaryNest b) body''

lowerFullySequentialBlock :: EnvReader m => SBlock n -> m n (DestBlock n)
lowerFullySequentialBlock b = liftAtomSubstBuilder do
  resultDestTy <- RawRefTy <$> substM (getType b)
  withFreshBinder (getNameHint @String "ans") resultDestTy \destBinder -> do
    Abs destBinder <$> buildBlock do
      let dest = Var $ sink $ binderVar destBinder
      lowerBlockWithDest dest b $> UnitVal
{-# SCC lowerFullySequentialBlock #-}

lowerFullySequentialNoDest :: EnvReader m => SLam n -> m n (SLam n)
lowerFullySequentialNoDest (LamExpr bs body) = liftEnvReaderM $ do
  refreshAbs (Abs bs body) \bs' body' -> do
    body'' <- lowerFullySequentialBlockNoDest body'
    return $ LamExpr bs' body''

lowerFullySequentialBlockNoDest :: EnvReader m => SBlock n -> m n (SBlock n)
lowerFullySequentialBlockNoDest b = liftAtomSubstBuilder $ buildBlock $ lowerBlock b
{-# SCC lowerFullySequentialBlockNoDest #-}

data LowerTag
type LowerM = AtomSubstBuilder LowerTag SimpIR

instance NonAtomRenamer (LowerM i o) i o where renameN = substM

instance ExprVisitorEmits (LowerM i o) SimpIR i o where
  visitExprEmits = lowerExpr

instance Visitor (LowerM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits

lowerExpr :: Emits o => SExpr i -> LowerM i o (SAtom o)
lowerExpr expr = emitExpr =<< case expr of
  TabCon Nothing ty els -> lowerTabCon Nothing ty els
  PrimOp (Hof (TypedHof (EffTy _ resultTy) (For dir ixDict body))) -> do
    resultTy' <- substM resultTy
    lowerFor resultTy' Nothing dir ixDict body
  -- this case is important because this pass changes effects
  PrimOp (Hof (TypedHof _ hof)) ->
    PrimOp . Hof <$> (visitGeneric hof >>= mkTypedHof)
  Case e alts (EffTy _ ty) -> lowerCase Nothing e alts ty
  _ -> visitGeneric expr

lowerBlock :: Emits o => SBlock i -> LowerM i o (SAtom o)
lowerBlock = visitBlockEmits

type Dest = Atom

lowerFor
  :: Emits o
  => SType o -> Maybe (Dest SimpIR o) -> ForAnn -> IxType SimpIR i -> LamExpr SimpIR i
  -> LowerM i o (SExpr o)
lowerFor ansTy maybeDest dir ixTy (UnaryLamExpr (ib:>ty) body) = do
  ixTy' <- substM ixTy
  ty' <- substM ty
  case isSingletonType ansTy of
    True -> do
      body' <- buildUnaryLamExpr noHint (PairTy ty' UnitTy) \b' -> do
        (i, _) <- fromPair $ Var b'
        extendSubst (ib @> SubstVal i) $ lowerBlock body $> UnitVal
      void $ emitSeq dir ixTy' UnitVal body'
      Atom . fromJust <$> singletonTypeVal ansTy
    False -> do
      initDest <- ProdVal . (:[]) <$> case maybeDest of
        Just  d -> return d
        Nothing -> emitOp $ DAMOp $ AllocDest ansTy
      let destTy = getType initDest
      body' <- buildUnaryLamExpr noHint (PairTy ty' destTy) \b' -> do
        (i, destProd) <- fromPair $ Var b'
        dest <- normalizeProj (ProjectProduct 0) destProd
        idest <- emitOp =<< mkIndexRef dest i
        extendSubst (ib @> SubstVal i) $ lowerBlockWithDest idest body $> UnitVal
      ans <- emitSeq dir ixTy' initDest body' >>= getProj 0
      return $ PrimOp $ DAMOp $ Freeze ans
lowerFor _ _ _ _ _ = error "expected a unary lambda expression"

lowerTabCon :: forall i o. Emits o
  => Maybe (Dest SimpIR o) -> SType i -> [SAtom i] -> LowerM i o (SExpr o)
lowerTabCon maybeDest tabTy elems = do
  tabTy'@(TabPi (TabPiType dict (_:>t) _)) <- substM tabTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitExpr $ PrimOp $ DAMOp $ AllocDest tabTy'
  Abs bord ufoBlock <- buildAbs noHint IdxRepTy \ord -> do
    buildBlock $ unsafeFromOrdinal (sink $ IxType t dict) $ Var $ sink ord
  -- This is emitting a chain of RememberDest ops to force `dest` to be used
  -- linearly, and to force reads of the `Freeze dest'` result not to be
  -- reordered in front of the writes.
  -- TODO: We technically don't need to sequentialize the writes, since the
  -- slices are all independent of each other.  Do we need a new `JoinDests`
  -- operation to represent that pattern?
  let go incoming_dest [] = return incoming_dest
      go incoming_dest ((ord, e):rest) = do
        i <- dropSubst $ extendSubst (bord@>SubstVal (IdxRepVal (fromIntegral ord))) $
          lowerBlock ufoBlock
        carried_dest <- buildRememberDest "dest" incoming_dest \local_dest -> do
          idest <- indexRef (Var local_dest) (sink i)
          place (FullDest idest) =<< visitAtom e
          return UnitVal
        go carried_dest rest
  dest' <- go dest (enumerate elems)
  return $ PrimOp $ DAMOp $ Freeze dest'

lowerCase :: Emits o
  => Maybe (Dest SimpIR o) -> SAtom i -> [Alt SimpIR i] -> SType i
  -> LowerM i o (SExpr o)
lowerCase maybeDest scrut alts resultTy = do
  resultTy' <- substM resultTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitExpr $ PrimOp $ DAMOp $ AllocDest resultTy'
  scrut' <- visitAtom scrut
  dest' <- buildRememberDest "case_dest" dest \local_dest -> do
    alts' <- forM alts \(Abs (b:>ty) body) -> do
      ty' <- substM ty
      buildAbs (getNameHint b) ty' \b' ->
        extendSubst (b @> Rename (atomVarName b')) $
          buildBlock do
            lowerBlockWithDest (Var $ sink $ local_dest) body $> UnitVal
    eff' <- foldMapM (pure . getEffects) alts'
    void $ emitExpr $ Case (sink scrut') alts' (EffTy eff' UnitTy)
    return UnitVal
  return $ PrimOp $ DAMOp $ Freeze dest'

-- Destination-passing traversals
--
-- The idea here is to try to reuse the memory already allocated for outputs of surrounding
-- higher order functions for values produced inside nested blocks. As an example,
-- consider two perfectly nested for loops:
--
-- for i:(Fin 10).
--   v = for j:(Fin 20). ...
--   v
--
-- (binding of the for as v is necessary since Blocks end with Atoms).
--
-- The outermost loop will have to allocate the memory for a 2D array. But it would be
-- a waste if the inner loop kept allocating 20-element blocks only to copy them into
-- that full outermost buffer. Instead, we invoke lowerBlockWithDest on the body
-- of the i-loop, which will realize that v has a valid destination. Then,
-- lowerExprWithDest will be called at the for decl and will translate the j-loop
-- so that it never allocates scratch space for its result, but will put it directly in
-- the corresponding slice of the full 2D buffer.

type DestAssignment (i'::S) (o::S) = AtomNameMap SimpIR (ProjDest o) i'

data ProjDest o
  = FullDest (Dest SimpIR o)
  | ProjDest (NE.NonEmpty Projection) (Dest SimpIR o)  -- dest corresponds to the projection applied to name

instance SinkableE ProjDest where
  sinkingProofE = todoSinkableProof

lookupDest :: DestAssignment i' o -> SAtomName i' -> Maybe (ProjDest o)
lookupDest = flip lookupNameMap

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
--
-- XXX: When adding more cases, be careful about potentially repeated vars in the output!
decomposeDest :: Emits o => Dest SimpIR o -> SAtom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Var v -> return $ Just $ singletonNameMap (atomVarName v) $ FullDest dest
  ProjectElt _ p x -> do
    (ps, v) <- return $ asNaryProj p x
    return $ Just $ singletonNameMap (atomVarName v) $ ProjDest ps dest
  _ -> return Nothing

lowerBlockWithDest :: Emits o => Dest SimpIR o -> SBlock i -> LowerM i o (SAtom o)
lowerBlockWithDest dest (Block _ decls ans) = do
  decomposeDest dest ans >>= \case
    Nothing -> do
      ans' <- visitDeclsEmits decls $ visitAtom ans
      place (FullDest dest) ans'
      return ans'
    Just destMap -> do
      s <- getSubst
      case isDistinctNest decls of
        Nothing -> error "Non-distinct decls?"
        Just DistinctBetween -> do
          s' <- traverseDeclNestWithDestS destMap s decls
          -- But we have to emit explicit writes, for all the vars that are not defined in decls!
          forM_ (toListNameMap $ hoistFilterNameMap decls destMap) \(n, d) -> do
            x <- case s ! n of
              Rename v -> Var <$> toAtomVar v
              SubstVal a -> return a
            place d x
          withSubst s' $ substM ans

traverseDeclNestWithDestS
  :: forall i i' l o. (Emits o, DistinctBetween l i')
  => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest (Decl SimpIR) l i'
  -> LowerM i o (Subst AtomSubstVal i' o)
traverseDeclNestWithDestS destMap s = \case
  Empty -> return s
  Nest (Let b (DeclBinding ann expr)) rest -> do
    DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
    let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
    expr' <- withSubst s $ lowerExprWithDest maybeDest expr
    v <- emitDecl (getNameHint b) ann expr'
    traverseDeclNestWithDestS destMap (s <>> (b @> Rename (atomVarName v))) rest

lowerExprWithDest :: forall i o. Emits o => Maybe (ProjDest o) -> SExpr i -> LowerM i o (SExpr o)
lowerExprWithDest dest expr = case expr of
  TabCon Nothing ty els -> lowerTabCon tabDest ty els
  PrimOp (Hof (TypedHof (EffTy _ ansTy) (For dir ixDict body))) -> do
    ansTy' <- substM ansTy
    lowerFor ansTy' tabDest dir ixDict body
  PrimOp (Hof (TypedHof (EffTy _ ty) (RunWriter Nothing m body))) -> do
    PairTy _ ansTy <- visitType ty
    traverseRWS ansTy body \ref' body' -> do
      m' <- visitGeneric m
      return $ RunWriter ref' m' body'
  PrimOp (Hof (TypedHof (EffTy _ ty) (RunState Nothing s body))) -> do
    PairTy _ ansTy <- visitType ty
    traverseRWS ansTy body \ref' body' -> do
      s' <- visitAtom s
      return $ RunState ref' s' body'
  -- this case is important because this pass changes effects
  PrimOp (Hof (TypedHof _ hof)) -> do
    hof' <- PrimOp . Hof <$> (visitGeneric hof >>= mkTypedHof)
    placeGeneric hof'
  Case e alts (EffTy _ ty) -> case dest of
    Nothing -> lowerCase Nothing e alts ty
    Just (FullDest d) -> lowerCase (Just d) e alts ty
    Just d -> do
      ans <- lowerCase Nothing e alts ty >>= emitExprToAtom
      place d ans
      return $ Atom ans
  _ -> generic
  where
    tabDest = dest <&> \case FullDest d -> d; ProjDest _ _ -> error "unexpected projection"

    generic = visitGeneric expr >>= placeGeneric

    placeGeneric e = do
      case dest of
        Nothing -> return e
        Just d  -> do
          ans <- Var <$> emit e
          place d ans
          return $ Atom ans

    traverseRWS
      :: SType o -> LamExpr SimpIR i
      -> (Maybe (Dest SimpIR o) -> LamExpr SimpIR o -> LowerM i o (Hof SimpIR o))
      -> LowerM i o (SExpr o)
    traverseRWS referentTy (LamExpr (BinaryNest hb rb) body) cont = do
      unpackRWSDest dest >>= \case
        Nothing -> generic
        Just (bodyDest, refDest) -> do
          hof <- cont refDest =<<
            buildEffLam (getNameHint rb) referentTy \hb' rb' ->
              extendRenamer (hb@>atomVarName hb' <.> rb@>atomVarName rb') do
                case bodyDest of
                  Nothing -> lowerBlock body
                  Just bd -> lowerBlockWithDest (sink bd) body
          PrimOp . Hof <$> mkTypedHof hof

    traverseRWS _ _ _ = error "Expected a binary lambda expression"

    unpackRWSDest = \case
      Nothing -> return Nothing
      Just d -> case d of
        FullDest fd -> do
          bd <- getProjRef (ProjectProduct 0) fd
          rd <- getProjRef (ProjectProduct 1) fd
          return $ Just (Just bd, Just rd)
        ProjDest (ProjectProduct 0 NE.:| []) pd -> return $ Just (Just pd, Nothing)
        ProjDest (ProjectProduct 1 NE.:| []) pd -> return $ Just (Nothing, Just pd)
        ProjDest _ _ -> return Nothing

place :: Emits o => ProjDest o -> SAtom o -> LowerM i o ()
place pd x = case pd of
  FullDest d   -> void $ emitOp $ DAMOp $ Place d x
  ProjDest p d -> do
    x' <- normalizeNaryProj (NE.toList p) x
    void $ emitOp $ DAMOp $ Place d x'

-- === Vectorization ===

-- WATCH OUT! This vectorization assumes that all raw references represent
-- destinations, and so no Place operations can cause write conflicts.

-- TODO: Local vector values? We might want to pack short and pure for loops into vectors,
-- to support things like float3 etc.
data Stability
  = Uniform    -- constant across vectorized dimension
  | Varying    -- varying across vectorized dimension
  | Contiguous -- varying, but contiguous across vectorized dimension
  | ProdStability [Stability]
  deriving (Eq, Show)

data VSubstValC (c::C) (n::S) where
  VVal   :: Stability -> SAtom n -> VSubstValC (AtomNameC SimpIR) n
  VRename :: Name c n -> VSubstValC c n

type VAtom = VSubstValC (AtomNameC SimpIR)
instance SinkableV VSubstValC
instance SinkableE (VSubstValC c) where
  sinkingProofE fresh (VVal s x) = VVal s $ sinkingProofE fresh x
  sinkingProofE fresh (VRename n) = VRename $ sinkingProofE fresh n

instance Pretty (VSubstValC c n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (VSubstValC c n) where
  prettyPrec (VVal s atom) = atPrec LowestPrec $ "@" <> viaShow s <+> pretty atom
  prettyPrec (VRename v) = atPrec LowestPrec $ "Rename" <+> pretty v

newtype TopVectorizeM (i::S) (o::S) (a:: *) = TopVectorizeM
  { runTopVectorizeM ::
      SubstReaderT Name
       (ReaderT1 (LiftE Word32)
         (StateT1 (LiftE Errs) (BuilderT SimpIR FallibleM))) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, MonadReader (LiftE Word32 o)
           , MonadState (LiftE Errs o), Fallible, ScopeReader, EnvReader
           , EnvExtender, Builder SimpIR, ScopableBuilder SimpIR, Catchable
           , SubstReader Name)

vectorizeLoops :: EnvReader m => Word32 -> DestLamExpr n -> m n (DestLamExpr n, Errs)
vectorizeLoops width (LamExpr bsDestB body) = liftEnvReaderM do
  case popNest bsDestB of
    Just (PairB bs b) ->
      refreshAbs (Abs bs (Abs b body)) \bs' body' -> do
        (Abs b'' body'', errs) <- liftTopVectorizeM width $ vectorizeLoopsDestBlock body'
        return $ (LamExpr (bs' >>> UnaryNest b'') body'', errs)
    Nothing -> error "expected a trailing dest binder"

liftTopVectorizeM :: (EnvReader m)
  => Word32 -> TopVectorizeM i i a -> m i (a, Errs)
liftTopVectorizeM vectorByteWidth action = do
  fallible <- liftBuilderT $
    flip runStateT1 mempty $ runReaderT1 (LiftE vectorByteWidth) $
      runSubstReaderT idSubst $ runTopVectorizeM action
  case runFallibleM fallible of
    -- The failure case should not occur: vectorization errors should have been
    -- caught inside `vectorizeLoopsDecls` (and should have been added to the
    -- `Errs` state of the `StateT` instance that is run with `runStateT` above).
    Failure errs -> error $ pprint errs
    Success (a, (LiftE errs)) -> return $ (a, errs)

addVectErrCtx :: Fallible m => String -> String -> m a -> m a
addVectErrCtx name payload m =
  let ctx = mempty { messageCtx = ["In `" ++ name ++ "`:\n" ++ payload] }
  in addErrCtx ctx m

throwVectErr :: Fallible m => String -> m a
throwVectErr msg = throwErr (Err MiscErr mempty msg)

prependCtxToErrs :: ErrCtx -> Errs -> Errs
prependCtxToErrs ctx (Errs errs) =
  Errs $ map (\(Err ty ctx' msg) -> Err ty (ctx <> ctx') msg) errs

vectorizeLoopsDestBlock :: DestBlock i
  -> TopVectorizeM i o (DestBlock o)
vectorizeLoopsDestBlock (Abs (destb:>destTy) body) = do
  destTy' <- renameM destTy
  withFreshBinder (getNameHint destb) destTy' \destb' -> do
    extendRenamer (destb @> binderName destb') do
      Abs destb' <$> buildBlock (vectorizeLoopsBlock body)
{-# SCC vectorizeLoopsDestBlock #-}

vectorizeLoopsBlock :: (Emits o)
  => Block SimpIR i -> TopVectorizeM i o (SAtom o)
vectorizeLoopsBlock (Block _ decls ans) =
  vectorizeLoopsDecls decls $ renameM ans

vectorizeLoopsDecls :: (Emits o)
  => Nest SDecl i i' -> TopVectorizeM i' o a -> TopVectorizeM i o a
vectorizeLoopsDecls nest cont =
  case nest of
    Empty -> cont
    Nest (Let b (DeclBinding ann expr)) rest -> do
      v <- emitDecl (getNameHint b) ann =<< vectorizeLoopsExpr expr
      extendSubst (b @> atomVarName v) $
        vectorizeLoopsDecls rest cont

vectorizeLoopsExpr :: (Emits o) => SExpr i -> TopVectorizeM i o (SExpr o)
vectorizeLoopsExpr expr = do
  LiftE vectorByteWidth <- ask
  narrowestTypeByteWidth <- getNarrowestTypeByteWidth =<< renameM expr
  let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
  case expr of
    PrimOp (DAMOp (Seq _ dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal n))) dest@(ProdVal [_]) body))
      | n `mod` loopWidth == 0 -> (do
          Distinct <- getDistinct
          let vn = n `div` loopWidth
          body' <- vectorizeSeq loopWidth body
          dest' <- renameM dest
          seqOp <- mkSeq dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal vn))) dest' body'
          return $ PrimOp $ DAMOp seqOp)
        `catchErr` \errs -> do
            let msg = "In `vectorizeLoopsDecls`:\nExpr:\n" ++ pprint expr
                ctx = mempty { messageCtx = [msg] }
                errs' = prependCtxToErrs ctx errs
            modify (<> LiftE errs')
            dest' <- renameM dest
            body' <- renameM body
            seqOp <- mkSeq dir (IxType IdxRepTy (IxDictRawFin (IdxRepVal n))) dest' body'
            return $ PrimOp $ DAMOp seqOp
    PrimOp (Hof (TypedHof _ (RunReader item (BinaryLamExpr hb' refb' body)))) -> do
      item' <- renameM item
      itemTy <- return $ getType item'
      lam <- buildEffLam noHint itemTy \hb refb ->
        extendRenamer (hb' @> atomVarName hb) do
          extendRenamer (refb' @> atomVarName refb) do
            vectorizeLoopsBlock body
      PrimOp . Hof <$> mkTypedHof (RunReader item' lam)
    _ -> renameM expr

-- Vectorizing a loop with an effect is safe when the operation reordering
-- produced by vectorization doesn't change the semantics.  This is guaranteed
-- to happen when:
-- - It's the Init effect (because the writes are non-aliasing), or
-- - It's the Reader effect, or
-- - Every reference in the effect is accessed in non-aliasing
--   fashion across iterations (e.g., for i. ... ref!i ...), or
-- - It's a Writer effect with a commutative monoid, or
-- - It's a Writer effect and the body writes to each set of
--   potentially overlapping references in scope at most once
--   (and the vector operations have in-order reductions
--   available)
-- - The Exception effect should have been transformed away by now
-- - The IO effect is in general not safe
-- This check doesn't have enough information to test the above,
-- but we crudely approximate for now.
vectorSafeEffect :: EffectRow SimpIR n -> Bool
vectorSafeEffect (EffectRow effs NoTail) = all safe $ eSetToList effs where
  safe InitEffect = True
  safe (RWSEffect Reader _) = True
  safe _ = False

vectorizeSeq :: Word32 -> LamExpr SimpIR i -> TopVectorizeM i o (LamExpr SimpIR o)
vectorizeSeq loopWidth (UnaryLamExpr (b:>ty) body) = do
  if vectorSafeEffect (getEffects body)
    then do
      (_, ty') <- case ty of
        ProdTy [ixTy, ref] -> do
          ixTy' <- renameM ixTy
          ref' <- renameM ref
          return (ixTy', ProdTy [IdxRepTy, ref'])
        _ -> error "Unexpected seq binder type"
      liftVectorizeM loopWidth $
        buildUnaryLamExpr (getNameHint b) ty' \ci -> do
          -- XXX: we're assuming `Fin n` here
          (viOrd, dest) <- fromPair $ Var ci
          iOrd <- imul viOrd $ IdxRepVal loopWidth
          extendSubst (b @> VVal (ProdStability [Contiguous, ProdStability [Uniform]]) (PairVal iOrd dest)) $
            vectorizeBlock body $> UnitVal
    else throwVectErr "Effectful loop vectorization not implemented!"
vectorizeSeq _ _ = error "expected a unary lambda expression"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM ::
    SubstReaderT VSubstValC (BuilderT SimpIR (ReaderT Word32 FallibleM)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail
           , SubstReader VSubstValC , Builder SimpIR, EnvReader, EnvExtender
           , ScopeReader, ScopableBuilder SimpIR)

liftVectorizeM :: (SubstReader Name m, EnvReader (m i), Fallible (m i o))
  => Word32 -> VectorizeM i o a -> m i o a
liftVectorizeM loopWidth action = do
  subst <- getSubst
  act <- liftBuilderT $ runSubstReaderT (newSubst $ vSubst subst) $ runVectorizeM action
  let fallible = flip runReaderT loopWidth act
  case runFallibleM fallible of
    Success a -> return a
    Failure errs -> throwErrs errs  -- re-raise inside ambient monad
  where
    vSubst subst val = VRename $ subst ! val

getLoopWidth :: VectorizeM i o Word32
getLoopWidth = VectorizeM $ SubstReaderT $ ReaderT $ const $ ask

vectorizeBlock :: Emits o => SBlock i -> VectorizeM i o (VAtom o)
vectorizeBlock block@(Block _ decls (ans :: SAtom i')) =
  addVectErrCtx "vectorizeBlock" ("Block:\n" ++ pprint block) $
    go decls
    where
      go :: Emits o => Nest SDecl i i' -> VectorizeM i o (VAtom o)
      go = \case
        Empty -> vectorizeAtom ans
        Nest (Let b (DeclBinding _ expr)) rest -> do
          v <- vectorizeExpr expr
          extendSubst (b @> v) $ go rest

vectorizeExpr :: Emits o => SExpr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = addVectErrCtx "vectorizeExpr" ("Expr:\n" ++ pprint expr) do
  case expr of
    TabApp _ tbl [ix] -> do
      VVal Uniform tbl' <- vectorizeAtom tbl
      VVal Contiguous ix' <- vectorizeAtom ix
      case getType tbl' of
        TabTy _ tb a -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Varying <$> emitOp (VectorOp $ VectorIdx tbl' ix' vty)
        tblTy -> do
          throwVectErr $ "bad type: " ++ pprint tblTy ++ "\ntbl' : " ++ pprint tbl'
    Atom atom -> vectorizeAtom atom
    PrimOp op -> vectorizePrimOp op
    _ -> throwVectErr $ "Cannot vectorize expr: " ++ pprint expr

vectorizeDAMOp :: Emits o => DAMOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeDAMOp op =
  case op of
    Place ref' val' -> do
      VVal vref ref <- vectorizeAtom ref'
      sval@(VVal vval val) <- vectorizeAtom val'
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emitExpr $ PrimOp $ DAMOp $ Place ref val
        (Uniform   , _         ) -> throwVectErr "Write conflict? This should never happen!"
        (Varying   , _         ) -> throwVectErr "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emitExpr $ PrimOp $ DAMOp $ Place ref val
        (Contiguous, Contiguous) -> emitExpr . PrimOp . DAMOp . Place ref =<< ensureVarying sval
        _ -> throwVectErr "Not implemented yet"
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeRefOp :: Emits o => SAtom i -> RefOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizeRefOp ref' op =
  case op of
    MAsk -> do
      -- TODO A contiguous reference becomes a vector load producing a varying
      -- result.
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Uniform <$> emitOp (RefOp ref MAsk)
    IndexRef _ i' -> do
      VVal Uniform ref <- vectorizeAtom ref'
      VVal Contiguous i <- vectorizeAtom i'
      case getType ref of
        TC (RefType _ (TabTy _ tb a)) -> do
          vty <- getVectorType =<< case hoist tb a of
            HoistSuccess a' -> return a'
            HoistFailure _  -> throwVectErr "Can't vectorize dependent table application"
          VVal Contiguous <$> emitOp (VectorOp $ VectorSubref ref i vty)
        refTy -> do
          throwVectErr do
            "bad type: " ++ pprint refTy ++ "\nref' : " ++ pprint ref'
    _ -> throwVectErr $ "Can't vectorize op: " ++ pprint (RefOp ref' op)

vectorizePrimOp :: Emits o => PrimOp SimpIR i -> VectorizeM i o (VAtom o)
vectorizePrimOp op = case op of
  UnOp opk arg -> do
    sx@(VVal vx x) <- vectorizeAtom arg
    let v = case vx of Uniform -> Uniform; _ -> Varying
    x' <- if vx /= v then ensureVarying sx else return x
    VVal v <$> emitOp (UnOp opk x')
  BinOp opk arg1 arg2 -> do
    sx@(VVal vx x) <- vectorizeAtom arg1
    sy@(VVal vy y) <- vectorizeAtom arg2
    let v = case (vx, vy) of (Uniform, Uniform) -> Uniform; _ -> Varying
    x' <- if vx /= v then ensureVarying sx else return x
    y' <- if vy /= v then ensureVarying sy else return y
    VVal v <$> emitOp (BinOp opk x' y')
  MiscOp (CastOp tyArg arg) -> do
    ty <- vectorizeType tyArg
    VVal vx x <- vectorizeAtom arg
    ty' <- case vx of
      Uniform    -> return ty
      Varying    -> getVectorType ty
      Contiguous -> return ty
      ProdStability _ -> throwVectErr "Unexpected cast of product type"
    VVal vx <$> emitOp (MiscOp $ CastOp ty' x)
  DAMOp op' -> vectorizeDAMOp op'
  RefOp ref op' -> vectorizeRefOp ref op'
  MemOp (PtrOffset arg1 arg2) -> do
    VVal Uniform ptr    <- vectorizeAtom arg1
    VVal Contiguous off <- vectorizeAtom arg2
    VVal Contiguous <$> emitOp (MemOp $ PtrOffset ptr off)
  MemOp (PtrLoad arg) -> do
    VVal Contiguous ptr <- vectorizeAtom arg
    BaseTy (PtrType (addrSpace, a)) <- return $ getType ptr
    BaseTy av <- getVectorType $ BaseTy a
    ptr' <- emitOp $ MiscOp $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
    VVal Varying <$> emitOp (MemOp $ PtrLoad ptr')
  -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
  -- being picky about the IO-inducing ops it supports, and expect it to
  -- complain about FFI calls and the like.
  Hof (TypedHof _ (RunIO body)) -> do
  -- TODO: buildBlockAux?
    Abs decls (LiftE vy `PairE` yWithTy) <- buildScoped do
      VVal vy y <- vectorizeBlock body
      PairE (LiftE vy) <$> withType y
    body' <- absToBlock =<< computeAbsEffects (Abs decls yWithTy)
    VVal vy <$> emitHof (RunIO body')
  _ -> throwVectErr $ "Can't vectorize op: " ++ pprint op

vectorizeType :: SType i -> VectorizeM i o (SType o)
vectorizeType t = do
  subst <- getSubst
  fmapNamesM (uniformSubst subst) t

vectorizeAtom :: SAtom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = addVectErrCtx "vectorizeAtom" ("Atom:\n" ++ pprint atom) do
  case atom of
    Var v -> lookupSubstM (atomVarName v) >>= \case
      VRename v' -> VVal Uniform . Var <$> toAtomVar v'
      v' -> return v'
    -- Vectors of base newtypes are already newtype-stripped.
    ProjectElt _ (ProjectProduct i) x -> do
      VVal vv x' <- vectorizeAtom x
      ov <- case vv of
        ProdStability sbs -> return $ sbs !! i
        _ -> throwVectErr "Invalid projection"
      x'' <- normalizeProj (ProjectProduct i) x'
      return $ VVal ov x''
    ProjectElt _ UnwrapNewtype _ -> error "Shouldn't have newtypes left" -- TODO: check statically
    Con (Lit l) -> return $ VVal Uniform $ Con $ Lit l
    _ -> do
      subst <- getSubst
      VVal Uniform <$> fmapNamesM (uniformSubst subst) atom

uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
uniformSubst subst n = case subst ! n of
  VVal Uniform x -> SubstVal x
  VRename name -> Rename name
  -- TODO(nrink): Throw instead of `error`.
  _ -> error "Can't vectorize atom"

getVectorType :: SType o -> VectorizeM i o (SType o)
getVectorType ty = addVectErrCtx "getVectorType" ("Type:\n" ++ pprint ty) do
  case ty of
    BaseTy (Scalar sbt) -> do
      els <- getLoopWidth
      return $ BaseTy $ Vector [els] sbt
    -- TODO: Should we support tables?
    _ -> throwVectErr $ "Can't make a vector of " ++ pprint ty

ensureVarying :: Emits o => VAtom o -> VectorizeM i o (SAtom o)
ensureVarying (VVal s val) = case s of
  Varying -> return val
  Uniform -> do
    vty <- getVectorType $ getType val
    emitOp $ VectorOp $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    let ty = getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emitOp $ VectorOp $ VectorBroadcast val vty
        iota <- emitOp $ VectorOp $ VectorIota vty
        emitOp $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> throwVectErr "Not implemented"
  ProdStability _ -> throwVectErr "Not implemented"
ensureVarying (VRename v) = do
  x <- Var <$> toAtomVar v
  ensureVarying (VVal Uniform x)

-- === Extensions to the name system ===

class DistinctBetween (n::S) (l::S)
instance DistinctBetween VoidS VoidS

data DistinctBetweenEvidence (n::S) (l::S) where
  DistinctBetween :: DistinctBetween n l => DistinctBetweenEvidence n l

fabricateDistinctBetweenEvidence :: forall n l. DistinctBetweenEvidence n l
fabricateDistinctBetweenEvidence = unsafeCoerce $ DistinctBetween @VoidS @VoidS

sinkBetween :: DistinctBetween n l => e n -> e l
sinkBetween = unsafeCoerceE

shortenBetween :: forall l n n' b. (ProvesExt b, Ext n' l, DistinctBetween n l) => b n n' -> DistinctBetweenEvidence n' l
shortenBetween _ = unsafeCoerce $ DistinctBetween @n @l

isDistinctNest :: Nest SDecl n l -> Maybe (DistinctBetweenEvidence n l)
isDistinctNest nest = case noShadows $ toScopeFrag nest of
  True  -> Just $ fabricateDistinctBetweenEvidence
  False -> Nothing

-- === computing byte widths ===

newtype CalcWidthM i o a = CalcWidthM {
  runTypeWidthM :: SubstReaderT Name (StateT1 (LiftE Word32) EnvReaderM) i o a}
  deriving (Functor, Applicative, Monad, SubstReader Name, EnvExtender,
            ScopeReader, EnvReader, MonadState (LiftE Word32 o))

instance NonAtomRenamer (CalcWidthM i o) i o where renameN = renameM
instance Visitor (CalcWidthM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamNoEmits

instance ExprVisitorNoEmits (CalcWidthM i o) SimpIR i o where
  visitExprNoEmits expr = case expr of
    PrimOp (Hof     _) -> fallback
    PrimOp (DAMOp _  ) -> fallback
    PrimOp (RefOp _ _) -> fallback
    PrimOp _ -> do
      expr' <- renameM expr
      let ty = getType expr'
      modify (\(LiftE x) -> LiftE $ min (typeByteWidth ty) x)
      return expr'
    _ -> fallback
    where fallback = visitGeneric expr

typeByteWidth :: SType n -> Word32
typeByteWidth ty = case ty of
 TC (BaseType bt) -> case bt of
  -- Currently only support vectorization of scalar types (cf. `getVectorType` above):
  Scalar _ -> fromInteger . toInteger $ sizeOf bt
  _ -> maxWord32
 _ -> maxWord32

maxWord32 :: Word32
maxWord32 = maxBound

getNarrowestTypeByteWidth :: (EnvReader m) => Expr SimpIR n -> m n Word32
getNarrowestTypeByteWidth x = do
  (_, LiftE result) <-  liftEnvReaderM $ runStateT1
    (runSubstReaderT idSubst $ runTypeWidthM $ visitExprNoEmits x) (LiftE maxWord32)
  if result == maxWord32
    then return 1
    else return result
