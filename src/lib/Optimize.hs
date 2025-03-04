-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Optimize
  ( optimize, peepholeOp, peepholeExpr, hoistLoopInvariant, dceTop, foldCast ) where

import Data.Functor
import Data.Word
import Data.Bits
import Data.Bits.Floating
import Data.List
import Control.Monad
import Control.Monad.State.Strict
import GHC.Float

import Types.Core
import Types.Primitives
import MTL1
import Name
import Subst
import IRVariants
import Core
import CheapReduction
import Builder
import QueryType
import Util (iota)
import Err

optimize :: EnvReader m => STopLam n -> m n (STopLam n)
optimize = dceTop     -- Clean up user code
       >=> unrollLoops
       >=> dceTop     -- Clean up peephole-optimized code after unrolling
       >=> hoistLoopInvariant

-- === Peephole optimizations ===

peepholeOp :: PrimOp SimpIR o -> EnvReaderM o (SExpr o)
peepholeOp op = case op of
  MiscOp (CastOp (BaseTy (Scalar sTy)) (Con (Lit l))) -> return $ case foldCast sTy l of
    Just l' -> lit l'
    Nothing -> noop
  -- TODO: Support more unary and binary ops.
  BinOp IAdd l r -> return $ case (l, r) of
    -- TODO: Shortcut when either side is zero.
    (Con (Lit ll), Con (Lit rl)) -> case (ll, rl) of
      (Word32Lit lv, Word32Lit lr) -> lit $ Word32Lit $ lv + lr
      _ -> noop
    _ -> noop
  BinOp (ICmp cop) (Con (Lit ll)) (Con (Lit rl)) ->
    return $ lit $ Word8Lit $ fromIntegral $ fromEnum $ case (ll, rl) of
      (Int32Lit  lv, Int32Lit  rv) -> cmp cop lv rv
      (Int64Lit  lv, Int64Lit  rv) -> cmp cop lv rv
      (Word8Lit  lv, Word8Lit  rv) -> cmp cop lv rv
      (Word32Lit lv, Word32Lit rv) -> cmp cop lv rv
      (Word64Lit lv, Word64Lit rv) -> cmp cop lv rv
      _ -> error "Ill typed ICmp?"
  BinOp (FCmp cop) (Con (Lit ll)) (Con (Lit rl)) ->
    return $ lit $ Word8Lit $ fromIntegral $ fromEnum $ case (ll, rl) of
      (Float32Lit lv, Float32Lit rv) -> cmp cop lv rv
      (Float64Lit lv, Float64Lit rv) -> cmp cop lv rv
      _ -> error "Ill typed FCmp?"
  BinOp BOr (Con (Lit (Word8Lit lv))) (Con (Lit (Word8Lit rv))) ->
    return $ lit $ Word8Lit $ lv .|. rv
  BinOp BAnd (Con (Lit (Word8Lit lv))) (Con (Lit (Word8Lit rv))) ->
    return $ lit $ Word8Lit $ lv .&. rv
  MiscOp (ToEnum ty (Con (Lit (Word8Lit tag)))) -> case ty of
    SumTy cases -> return $ Atom $ SumVal cases (fromIntegral tag) UnitVal
    _ -> error "Ill typed ToEnum?"
  MiscOp (SumTag (SumVal _ tag _)) -> return $ lit $ Word8Lit $ fromIntegral tag
  _ -> return noop
  where
    noop = PrimOp op
    lit = Atom . Con . Lit

    cmp :: Ord a => CmpOp -> a -> a -> Bool
    cmp = \case
      Less         -> (<)
      Greater      -> (>)
      Equal        -> (==)
      LessEqual    -> (<=)
      GreaterEqual -> (>=)

foldCast :: ScalarBaseType -> LitVal -> Maybe LitVal
foldCast sTy l = case sTy of
  -- TODO: Check that the casts relating to floating-point agree with the
  -- runtime behavior.  The runtime is given by the `ICastOp` case in
  -- ImpToLLVM.hs.  We should make sure that the Haskell functions here
  -- produce bitwise identical results to those instructions, by adjusting
  -- either this or that as called for.
  -- TODO: Also implement casts that may have unrepresentable results, i.e.,
  -- casting floating-point numbers to smaller floating-point numbers or to
  -- fixed-point.  Both of these necessarily have a much smaller dynamic range.
  Int32Type -> case l of
    Int32Lit  _  -> Just l
    Int64Lit  i  -> Just $ Int32Lit  $ fromIntegral i
    Word8Lit  i  -> Just $ Int32Lit  $ fromIntegral i
    Word32Lit i  -> Just $ Int32Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Int32Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Int64Type -> case l of
    Int32Lit  i  -> Just $ Int64Lit  $ fromIntegral i
    Int64Lit  _  -> Just l
    Word8Lit  i  -> Just $ Int64Lit  $ fromIntegral i
    Word32Lit i  -> Just $ Int64Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Int64Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word8Type -> case l of
    Int32Lit  i  -> Just $ Word8Lit  $ fromIntegral i
    Int64Lit  i  -> Just $ Word8Lit  $ fromIntegral i
    Word8Lit  _  -> Just l
    Word32Lit i  -> Just $ Word8Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Word8Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word32Type -> case l of
    Int32Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Int64Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Word8Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Word32Lit _  -> Just l
    Word64Lit i  -> Just $ Word32Lit $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word64Type -> case l of
    Int32Lit  i  -> Just $ Word64Lit $ fromIntegral (fromIntegral i :: Word32)
    Int64Lit  i  -> Just $ Word64Lit $ fromIntegral i
    Word8Lit  i  -> Just $ Word64Lit $ fromIntegral i
    Word32Lit i  -> Just $ Word64Lit $ fromIntegral i
    Word64Lit _  -> Just l
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Float32Type -> case l of
    Int32Lit  i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Int64Lit  i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Word8Lit  i  -> Just $ Float32Lit $ fromIntegral i
    Word32Lit i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Word64Lit i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Float32Lit _ -> Just l
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Float64Type -> case l of
    Int32Lit  i  -> Just $ Float64Lit $ fromIntegral i
    Int64Lit  i  -> Just $ Float64Lit $ fixUlp i $ fromIntegral i
    Word8Lit  i  -> Just $ Float64Lit $ fromIntegral i
    Word32Lit i  -> Just $ Float64Lit $ fromIntegral i
    Word64Lit i  -> Just $ Float64Lit $ fixUlp i $ fromIntegral i
    Float32Lit f -> Just $ Float64Lit $ float2Double f
    Float64Lit _ -> Just l
    PtrLit   _ _ -> Nothing
  where
    -- When casting an integer type to a floating-point type of lower precision
    -- (e.g., int32 to float32), GHC between 7.8.3 and 9.2.2 (exclusive) rounds
    -- toward zero, instead of rounding to nearest even like everybody else.
    -- See https://gitlab.haskell.org/ghc/ghc/-/issues/17231.
    --
    -- We patch this by manually checking the two adjacent floats to the
    -- candidate answer, and using one of those if the reverse cast is closer
    -- to the original input.
    --
    -- This rounds to nearest.  We round to nearest *even* by considering the
    -- candidates in decreasing order of the number of trailing zeros they
    -- exhibit when cast back to the original integer type.
    fixUlp :: forall a b w. (Num a, Integral a, FiniteBits a, RealFrac b, FloatingBits b w)
      => a -> b -> b
    fixUlp orig candidate = res where
      res = closest $ sortBy moreLowBits [candidate, candidatem1, candidatep1]
      candidatem1 = nextDown candidate
      candidatep1 = nextUp candidate
      closest = minimumBy (\ca cb -> err ca `compare` err cb)
      err cand = absdiff orig (round cand)
      absdiff a b = if a >= b then a - b else b - a
      moreLowBits a b =
        compare (0 - countTrailingZeros (round @b @a a))
                (0 - countTrailingZeros (round @b @a b))

peepholeExpr :: SExpr o -> EnvReaderM o (SExpr o)
peepholeExpr expr = case expr of
  PrimOp op -> peepholeOp op
  TabApp _ (Var (AtomVar t _)) [IdxRepVal ord] ->
    lookupAtomName t <&> \case
      LetBound (DeclBinding ann (TabCon Nothing tabTy elems))
        | ann /= NoInlineLet && isFinTabTy tabTy->
        -- It is not safe to assume that this index can always be simplified!
        -- For example, it might be coming from an unsafe_from_ordinal that is
        -- under a case branch that would be dead for all invalid indices.
        if 0 <= ord && fromIntegral ord < length elems
          then Atom $ elems !! fromIntegral ord
          else expr
      _ -> expr
  -- TODO: Apply a function to literals when it has a cheap body?
  -- Think, partial evaluation of threefry.
  _ -> return expr
  where isFinTabTy = \case
          TabPi (TabPiType (IxDictRawFin _) _ _) -> True
          _ -> False

-- === Loop unrolling ===

unrollLoops :: EnvReader m => STopLam n -> m n (STopLam n)
unrollLoops = liftLamExpr unrollLoopsBlock
{-# SCC unrollLoops #-}

unrollLoopsBlock :: EnvReader m => SBlock n -> m n (SBlock n)
unrollLoopsBlock b = liftM fst $
  liftBuilder $ runStateT1 (runSubstReaderT idSubst (runULM $ ulBlock b)) (ULS 0)

newtype ULS n = ULS Int deriving Show
newtype ULM i o a = ULM { runULM :: SubstReaderT AtomSubstVal (StateT1 ULS (BuilderM SimpIR)) i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder SimpIR, SubstReader AtomSubstVal,
            ScopableBuilder SimpIR, MonadState (ULS o))

instance SinkableE ULS where
  sinkingProofE _ (ULS c) = ULS c
instance HoistableState ULS where
  hoistState _ _ (ULS c) = (ULS c)
  {-# INLINE hoistState #-}

instance NonAtomRenamer (ULM i o) i o where renameN = substM
instance Visitor (ULM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits
instance ExprVisitorEmits (ULM i o) SimpIR i o where
  visitExprEmits = ulExpr

ulBlock :: SBlock i -> ULM i o (SBlock o)
ulBlock b = buildBlock $ visitBlockEmits b

emitSubstBlock :: Emits o => SBlock i -> ULM i o (SAtom o)
emitSubstBlock (Abs decls ans) = visitDeclsEmits decls $ visitAtom ans

-- TODO: Refine the cost accounting so that operations that will become
-- constant-foldable after inlining don't count towards it.
ulExpr :: Emits o => SExpr i -> ULM i o (SAtom o)
ulExpr expr = case expr of
  PrimOp (Hof (TypedHof _ (For Fwd ixTy body))) ->
    case ixTypeDict ixTy of
      IxDictRawFin (IdxRepVal n) -> do
        (body', bodyCost) <- withLocalAccounting $ visitLamEmits body
        -- We add n (in the form of (... + 1) * n) for the cost of the TabCon reconstructing the result.
        case (bodyCost + 1) * (fromIntegral n) <= unrollBlowupThreshold of
          True -> case body' of
            UnaryLamExpr b' block' -> do
              vals <- dropSubst $ forM (iota n) \i -> do
                extendSubst (b' @> SubstVal (IdxRepVal i)) $ emitSubstBlock block'
              inc $ fromIntegral n  -- To account for the TabCon we emit below
              getLamExprType body' >>= \case
                PiType (UnaryNest (tb:>_)) (EffTy _ valTy) -> do
                  let tabTy = TabPi $ TabPiType (IxDictRawFin (IdxRepVal n)) (tb:>IdxRepTy) valTy
                  emitExpr $ TabCon Nothing tabTy vals
                _ -> error "Expected `for` body to have a Pi type"
            _ -> error "Expected `for` body to be a lambda expression"
          False -> do
            inc bodyCost
            ixTy' <- visitGeneric ixTy
            emitHof $ For Fwd ixTy' body'
      _ -> nothingSpecial
  -- Avoid unrolling loops with large table literals
  TabCon _ _ els -> inc (length els) >> nothingSpecial
  _ -> nothingSpecial
  where
    inc i = modify \(ULS n) -> ULS (n + i)
    nothingSpecial = inc 1 >> (visitGeneric expr >>= liftEnvReaderM . peepholeExpr)
                     >>= emitExprToAtom
    unrollBlowupThreshold = 12
    withLocalAccounting m = do
      oldCost <- get
      ans <- put (ULS 0) *> m
      ULS newCost <- get
      put oldCost $> (ans, newCost)
    {-# INLINE withLocalAccounting #-}

-- === Loop invariant code motion ===

data LICMTag
type LICMM = AtomSubstBuilder LICMTag SimpIR

liftLICMM :: EnvReader m => LICMM n n a -> m n a
liftLICMM cont = liftAtomSubstBuilder cont

instance NonAtomRenamer (LICMM i o) i o where renameN = substM
instance Visitor (LICMM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits

instance ExprVisitorEmits (LICMM i o) SimpIR i o where
  visitExprEmits = licmExpr

hoistLoopInvariantBlock :: EnvReader m => SBlock n -> m n (SBlock n)
hoistLoopInvariantBlock body = liftLICMM $ buildBlock $ visitBlockEmits body
{-# SCC hoistLoopInvariantBlock #-}

hoistLoopInvariant :: EnvReader m => STopLam n -> m n (STopLam n)
hoistLoopInvariant = liftLamExpr hoistLoopInvariantBlock
{-# INLINE hoistLoopInvariant #-}

licmExpr :: Emits o => SExpr i -> LICMM i o (SAtom o)
licmExpr = \case
  PrimOp (DAMOp (Seq _ dir ix (ProdVal dests) (LamExpr (UnaryNest b) body))) -> do
    ix' <- substM ix
    dests' <- mapM visitAtom dests
    let numCarriesOriginal = length dests'
    Abs hdecls destsAndBody <- visitBinders (UnaryNest b) \(UnaryNest b') -> do
      -- First, traverse the block, to allow any Hofs inside it to hoist their own decls.
      Abs decls ans <- buildBlock $ visitBlockEmits body
      -- Now, we process the decls and decide which ones to hoist.
      liftEnvReaderM $ runSubstReaderT idSubst $
          seqLICM REmpty mempty (asNameBinder b') REmpty decls ans
    PairE (ListE extraDests) ab <- emitDecls $ Abs hdecls destsAndBody
    extraDests' <- mapM toAtomVar extraDests
    -- Append the destinations of hoisted Allocs as loop carried values.
    let dests'' = ProdVal $ dests' ++ (Var <$> extraDests')
    let carryTy = getType dests''
    let lbTy = case ix' of IxType ixTy _ -> PairTy ixTy carryTy
    extraDestsTyped <- forM extraDests' \(AtomVar d t) -> return (d, t)
    Abs extraDestBs (Abs lb bodyAbs) <- return $ abstractFreeVars extraDestsTyped ab
    body' <- withFreshBinder noHint lbTy \lb' -> do
      (oldIx, allCarries) <- fromPair $ Var $ binderVar lb'
      (oldCarries, newCarries) <- splitAt numCarriesOriginal <$> getUnpacked allCarries
      let oldLoopBinderVal = PairVal oldIx (ProdVal oldCarries)
      let s = extraDestBs @@> map SubstVal newCarries <.> lb @> SubstVal oldLoopBinderVal
      block <- applySubst s bodyAbs
      return $ UnaryLamExpr lb' block
    emitSeq dir ix' dests'' body'
  PrimOp (Hof (TypedHof _ (For dir ix (LamExpr (UnaryNest b) body)))) -> do
    ix' <- substM ix
    Abs hdecls destsAndBody <- visitBinders (UnaryNest b) \(UnaryNest b') -> do
      Abs decls ans <- buildBlock $ visitBlockEmits body
      liftEnvReaderM $ runSubstReaderT idSubst $
          seqLICM REmpty mempty (asNameBinder b') REmpty decls ans
    PairE (ListE []) (Abs lnb bodyAbs) <- emitDecls $ Abs hdecls destsAndBody
    ixTy <- substM $ binderType b
    body' <- withFreshBinder noHint ixTy \i -> do
      block <- applyRename (lnb@>binderName i) bodyAbs
      return $ UnaryLamExpr i block
    emitHof $ For dir ix' body'
  expr -> visitGeneric expr >>= emitExpr

seqLICM :: RNest SDecl n1 n2      -- hoisted decls
        -> [SAtomName n2]          -- hoisted dests
        -> AtomNameBinder SimpIR n2 n3   -- loop binder
        -> RNest SDecl n3 n4      -- loop-dependent decls
        -> Nest SDecl m1 m2       -- decls remaining to process
        -> SAtom m2               -- loop result
        -> SubstReaderT AtomSubstVal EnvReaderM m1 n4
             (Abs (Nest SDecl)            -- hoisted decls
                (PairE (ListE SAtomName)  -- hoisted allocs (these should go in the loop carry)
                       (Abs (AtomNameBinder SimpIR) -- loop binder
                            (Abs (Nest SDecl)       -- non-hoisted decls
                             SAtom))) n1)           -- final result
seqLICM !top !topDestNames !lb !reg decls ans = case decls of
  Empty -> do
    ans' <- substM ans
    return $ Abs (unRNest top) $ PairE (ListE $ reverse topDestNames) $ Abs lb $ Abs (unRNest reg) ans'
  Nest (Let bb binding) bs -> do
    binding' <- substM binding
    withFreshBinder (getNameHint bb) binding' \(bb':>_) -> do
      let b = Let bb' binding'
      let moveOn = extendRenamer (bb@>binderName bb') $
                     seqLICM top topDestNames lb (RNest reg b) bs ans
      case getEffects binding' of
        -- OPTIMIZE: We keep querying the ScopeFrag of lb and reg here, leading to quadratic runtime
        Pure -> case exchangeBs $ PairB (PairB lb reg) b of
          HoistSuccess (PairB b' lbreg@(PairB lb' reg')) -> do
            withSubscopeDistinct lbreg $ withExtEvidence b' $
              extendRenamer (bb@>sink (binderName b')) do
                extraTopDestNames <- return case b' of
                  Let bn (DeclBinding _ (PrimOp (DAMOp (AllocDest _)))) -> [binderName bn]
                  _ -> []
                seqLICM (RNest top b') (extraTopDestNames ++ sinkList topDestNames) lb' reg' bs ans
              where
          HoistFailure _ -> moveOn
        _ -> moveOn

-- === Dead code elimination ===

newtype FV n = FV (NameSet n) deriving (Semigroup, Monoid)
instance SinkableE FV where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableState FV where
  hoistState _ b (FV ns) = FV $ hoistFilterNameSet b ns
  {-# INLINE hoistState #-}

newtype DCEM n a = DCEM { runDCEM :: StateT1 FV EnvReaderM n a }
  deriving ( Functor, Applicative, Monad, EnvReader, ScopeReader
           , MonadState (FV n), EnvExtender)

dceTop :: EnvReader m => STopLam n -> m n (STopLam n)
dceTop = liftLamExpr dceBlock
{-# INLINE dceTop #-}

dceBlock :: EnvReader m => SBlock n -> m n (SBlock n)
dceBlock b = liftEnvReaderM $ evalStateT1 (runDCEM $ dceBlock' b) mempty
{-# SCC dceBlock #-}

class HasDCE (e::E) where
  dce :: e n -> DCEM n (e n)
  default dce :: VisitGeneric e SimpIR => e n -> DCEM n (e n)
  dce = visitGeneric

instance NonAtomRenamer (DCEM o) o o where renameN = dce
instance Visitor (DCEM o) SimpIR o o where
  visitType = dce
  visitAtom = dce
  visitLam  = dce
  visitPi   = dce

instance Color c => HasDCE (Name c) where
  dce n = modify (<> FV (freeVarsE n)) $> n

instance HasDCE SAtom where
  dce = \case
    Var n -> modify (<> FV (freeVarsE n)) $> Var n
    ProjectElt t i x -> ProjectElt <$> dce t <*> pure i <*> dce x
    atom -> visitAtomPartial atom

instance HasDCE SType where dce = visitTypePartial
instance HasDCE (PiType SimpIR) where
  dce (PiType bs effTy) = do
    dceBinders bs effTy \bs' effTy' -> PiType bs' <$> dce effTy'

instance HasDCE (LamExpr SimpIR) where
  dce (LamExpr bs e) = dceBinders bs e \bs' e' -> LamExpr bs' <$> dceBlock' e'

dceBinders
  :: (HoistableB b, BindsEnv b, RenameB b, RenameE e)
  => b n l -> e l
  -> (forall l'. b n l' -> e l' -> DCEM l' a)
  -> DCEM n a
dceBinders b e cont = do
  ans <- refreshAbs (Abs b e) \b' e' -> cont b' e'
  modify (<>FV (freeVarsB b))
  return ans
{-# INLINE dceBinders #-}

dceBlock' :: SBlock n -> DCEM n (SBlock n)
dceBlock' (Abs decls ans) = do
  -- The free vars accumulated in the state of DCEM should correspond to
  -- the free vars of the Abs of the block answer, by the decls traversed
  -- so far. dceNest takes care to uphold this invariant, but we temporarily
  -- reset the state to an empty map, just so that names from the surrounding
  -- block don't end up influencing elimination decisions here. Note that we
  -- restore the state (and accumulate free vars of the DCE'd block into it)
  -- right after dceNest.
  old <- get
  put mempty
  block <- dceNest decls ans
  modify (<> old)
  return block

wrapWithCachedFVs :: HoistableE e => e n -> DCEM n (CachedFVs e n)
wrapWithCachedFVs e = do
  FV fvs <- get
#ifdef DEX_DEBUG
  let fvsAreCorrect = nameSetRawNames fvs == nameSetRawNames (freeVarsE e)
#else
  -- Verification of this invariant defeats the performance benefits of
  -- avoiding the extra traversal (e.g. actually having linear complexity),
  -- so we only do that in debug builds.
  let fvsAreCorrect = True
#endif
  case fvsAreCorrect of
    True -> return $ UnsafeCachedFVs fvs e
    False -> error $ "Free variables were computed incorrectly."

hoistUsingCachedFVs :: (BindsNames b, HoistableE e) =>
  b n l -> e l -> DCEM l (HoistExcept (e n))
hoistUsingCachedFVs b e = hoistViaCachedFVs b <$> wrapWithCachedFVs e

data ElimResult n where
  ElimSuccess :: Abs (Nest SDecl) SAtom n -> ElimResult n
  ElimFailure :: SDecl n l -> Abs (Nest SDecl) SAtom l -> ElimResult n

dceNest :: Nest SDecl n l -> SAtom l -> DCEM n (Abs (Nest SDecl) SAtom n)
dceNest decls ans = case decls of
  Empty -> Abs Empty <$> dce ans
  Nest b@(Let _ decl) bs -> do
    -- Note that we only ever dce the abs below under this refreshAbs,
    -- which will remove any references to b upon exit (it happens
    -- because refreshAbs of StateT1 triggers hoistState, which we
    -- implement by deleting the entries that can't hoist).
    dceAttempt <- refreshAbs (Abs b (Abs bs ans)) \b' (Abs bs' ans') -> do
      below <- dceNest bs' ans'
      case isPure decl of
        False -> return $ ElimFailure b' below
        True  -> do
          hoistUsingCachedFVs b' below <&> \case
            HoistSuccess below' -> ElimSuccess below'
            HoistFailure _ -> ElimFailure b' below
    case dceAttempt of
      ElimSuccess below' -> return below'
      ElimFailure (Let b' decl') (Abs bs'' ans'') -> do
        decl'' <- dce decl'
        modify (<>FV (freeVarsB b'))
        return $ Abs (Nest (Let b' decl'') bs'') ans''

instance HasDCE (EffectRow   SimpIR)
instance HasDCE (DeclBinding SimpIR)
instance HasDCE (EffTy       SimpIR)
