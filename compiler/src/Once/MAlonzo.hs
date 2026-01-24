-- | Bridge module for MAlonzo-generated Agda code
--
-- This module provides the interface for the verified MAlonzo optimizer
-- and type checker. Code is extracted from formally verified Agda proofs via MAlonzo.
module Once.MAlonzo
  ( -- * Optimization
    optimizeMAlonzo
    -- * Conversion functions (for native backends)
  , toMAlonzoType
  , fromMAlonzoType
  , toMAlonzoIR
  , fromMAlonzoIR
  , getInputType
  , getOutputType
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IntMap
import Text.Read (readMaybe)

import qualified Once.IR as H
import qualified Once.Type as H

import qualified MAlonzo.Code.Once.IR as M
import qualified MAlonzo.Code.Once.Type as M
import qualified MAlonzo.Code.Once.Optimize as MO

-- | Optimize using MAlonzo (verified) optimizer
--
-- Uses the formally verified optimizer extracted from Agda via MAlonzo.
-- Non-CCC leaves (StringLit, Arith) are encoded as opaque Prims,
-- optimized, then restored. Prim is mapped directly (Agda treats it as opaque).
optimizeMAlonzo :: H.IR -> H.IR
optimizeMAlonzo ir =
  let (cleanIR, opaques) = extractOpaques ir
      mIR = toMAlonzoIR cleanIR
      mOptimized = MO.d_optimize_1386 (getInputType cleanIR) (getOutputType cleanIR) mIR
      result = fromMAlonzoIR mOptimized
  in restoreOpaques opaques result

-- | Extract opaque leaves (StringLit, Arith) from IR, replacing with numbered Prims.
-- The optimizer treats all Prim as opaque, so the round-trip is safe.
extractOpaques :: H.IR -> (H.IR, IntMap.IntMap H.IR)
extractOpaques ir = let (ir', _, m) = go 0 ir in (ir', m)
  where
    go :: Int -> H.IR -> (H.IR, Int, IntMap.IntMap H.IR)
    go n (H.StringLit t) =
      let key = T.pack ("__opaque_" ++ show n)
      in (H.Prim key H.TUnit H.TUnit, n + 1, IntMap.singleton n (H.StringLit t))
    go n (H.Arith nt air) =
      let key = T.pack ("__opaque_" ++ show n)
      in (H.Prim key H.TUnit H.TUnit, n + 1, IntMap.singleton n (H.Arith nt air))
    go n (H.Compose g f) =
      let (g', n1, m1) = go n g
          (f', n2, m2) = go n1 f
      in (H.Compose g' f', n2, IntMap.union m1 m2)
    go n (H.Pair f g) =
      let (f', n1, m1) = go n f
          (g', n2, m2) = go n1 g
      in (H.Pair f' g', n2, IntMap.union m1 m2)
    go n (H.Case f g) =
      let (f', n1, m1) = go n f
          (g', n2, m2) = go n1 g
      in (H.Case f' g', n2, IntMap.union m1 m2)
    go n (H.Curry name f) =
      let (f', n1, m1) = go n f
      in (H.Curry name f', n1, m1)
    go n other = (other, n, IntMap.empty)

-- | Restore opaque leaves after optimization.
-- Replaces Prim "__opaque_N" back with the original StringLit/Arith.
restoreOpaques :: IntMap.IntMap H.IR -> H.IR -> H.IR
restoreOpaques opaques = go
  where
    go (H.Prim name _ _)
      | Just n <- parseOpaqueKey name
      , Just orig <- IntMap.lookup n opaques = orig
    go (H.Compose g f) = H.Compose (go g) (go f)
    go (H.Pair f g) = H.Pair (go f) (go g)
    go (H.Case f g) = H.Case (go f) (go g)
    go (H.Curry name f) = H.Curry name (go f)
    go other = other

    parseOpaqueKey :: Text -> Maybe Int
    parseOpaqueKey t = T.stripPrefix "__opaque_" t >>= readMaybe . T.unpack

-- | Convert Haskell Type to MAlonzo Type
toMAlonzoType :: H.Type -> M.T_Type_32
toMAlonzoType t = case t of
  H.TUnit        -> M.C_Unit_34
  H.TVoid        -> M.C_Void_36
  H.TInt         -> M.C_Int_48
  H.TFloat       -> M.C_Float_50
  H.TBuffer      -> M.C_Buffer_54
  H.TProduct a b -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.TSum a b     -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.TArrow a b   -> M.C__'8658''91'_'93'__42 (toMAlonzoType a) M.C_Many_10 (toMAlonzoType b)  -- Default to Many for unrestricted arrows
  H.TEff a b     -> M.C_Eff_44 (toMAlonzoType a) (toMAlonzoType b)
  H.TFix f       -> M.C_Fix_46 (toMAlonzoType f)
  H.TVar n       -> M.C_TVar_56 n  -- MAlonzo uses Text directly
  -- Not representable in Agda's type system
  H.TString _    -> error "MAlonzo: TString not supported (use Str)"
  H.TApp _ _     -> error "MAlonzo: TApp not supported"

-- | Convert MAlonzo Type to Haskell Type
fromMAlonzoType :: M.T_Type_32 -> H.Type
fromMAlonzoType t = case t of
  M.C_Unit_34         -> H.TUnit
  M.C_Void_36         -> H.TVoid
  M.C_Int_48          -> H.TInt
  M.C_Float_50        -> H.TFloat
  M.C_Str_52          -> H.TString H.Utf8  -- Default to UTF-8
  M.C_Buffer_54       -> H.TBuffer
  M.C__'42'__38 a b   -> H.TProduct (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'43'__40 a b   -> H.TSum (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'8658''91'_'93'__42 a _q b -> H.TArrow (fromMAlonzoType a) (fromMAlonzoType b)  -- Ignore quantity
  M.C_Eff_44 a b      -> H.TEff (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Fix_46 f        -> H.TFix (fromMAlonzoType f)
  M.C_TVar_56 n       -> H.TVar n  -- MAlonzo uses Text directly

-- | Convert Haskell IR to MAlonzo IR
--
-- After elaboration, the IR contains CCC generators + Prim.
-- StringLit/Arith are pre-extracted as opaque Prims by extractOpaques.
-- Var/LocalVar/FunRef/Let should not appear (resolved during elaboration).
toMAlonzoIR :: H.IR -> M.T_IR_10
toMAlonzoIR ir = case ir of
  H.Id _            -> M.C_id_14
  H.Compose g f     -> M.C__'8728'__22 (getMiddleType g f) (toMAlonzoIR g) (toMAlonzoIR f)
  H.Fst _ _         -> M.C_fst_28
  H.Snd _ _         -> M.C_snd_34
  H.Pair f g        -> M.C_'10216'_'44'_'10217'_42 (toMAlonzoIR f) (toMAlonzoIR g) M.C_Stack_6
  H.Terminal _      -> M.C_terminal_66
  H.Inl _ _         -> M.C_inl_48 M.C_Stack_6
  H.Inr _ _         -> M.C_inr_54 M.C_Stack_6
  H.Case f g        -> M.C_'91'_'44'_'93'_62 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Initial _       -> M.C_initial_70
  H.Curry _ f       -> M.C_curry_78 (toMAlonzoIR f) M.C_Stack_6
  H.Apply _ _       -> M.C_apply_84
  H.Fold _          -> M.C_fold_88
  H.Unfold _        -> M.C_unfold_92
  -- Prim maps directly to Agda's Prim (treated as opaque by optimizer)
  H.Prim name _ _   -> M.C_Prim_104 name
  -- These should not appear after elaboration + extractOpaques
  H.Var _           -> error "MAlonzo: Var should not appear after elaboration"
  H.LocalVar _      -> error "MAlonzo: LocalVar should not appear after elaboration"
  H.FunRef _        -> error "MAlonzo: FunRef should not appear after elaboration"
  H.StringLit _     -> error "MAlonzo: StringLit should be extracted by extractOpaques"
  H.Let _ _ _       -> error "MAlonzo: Let should not appear after elaboration"
  H.Arith _ _       -> error "MAlonzo: Arith should be extracted by extractOpaques"

-- | Convert MAlonzo IR to Haskell IR
--
-- Note: Type information is lost in MAlonzo IR, so we use placeholder types.
-- This is fine because the C backend ignores type annotations (uses wildcards).
fromMAlonzoIR :: M.T_IR_10 -> H.IR
fromMAlonzoIR ir = case ir of
  M.C_id_14                       -> H.Id placeholder
  M.C__'8728'__22 _ g f           -> H.Compose (fromMAlonzoIR g) (fromMAlonzoIR f)
  M.C_fst_28                      -> H.Fst placeholder placeholder
  M.C_snd_34                      -> H.Snd placeholder placeholder
  M.C_'10216'_'44'_'10217'_42 f g _alloc -> H.Pair (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_terminal_66                 -> H.Terminal placeholder
  M.C_inl_48 _alloc               -> H.Inl placeholder placeholder
  M.C_inr_54 _alloc               -> H.Inr placeholder placeholder
  M.C_'91'_'44'_'93'_62 f g       -> H.Case (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_initial_70                  -> H.Initial placeholder
  M.C_curry_78 f _alloc           -> H.Curry "_" (fromMAlonzoIR f)
  M.C_apply_84                    -> H.Apply placeholder placeholder
  M.C_fold_88                     -> H.Fold placeholder
  M.C_unfold_92                   -> H.Unfold placeholder
  M.C_arr_98                      -> H.Id placeholder  -- arr ≡ id semantically
  M.C_Prim_104 name               -> H.Prim name H.TUnit H.TUnit
  where
    placeholder = H.TUnit  -- Type info is erased, use placeholder

-- | Get input type of an IR expression
getInputType :: H.IR -> M.T_Type_32
getInputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a b         -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.Snd a b         -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.Inl a _         -> toMAlonzoType a
  H.Inr _ b         -> toMAlonzoType b
  H.Terminal t      -> toMAlonzoType t
  H.Initial _       -> M.C_Void_36
  H.Apply a b       -> M.C__'42'__38 (M.C__'8658''91'_'93'__42 (toMAlonzoType a) M.C_Many_10 (toMAlonzoType b)) (toMAlonzoType a)
  H.Fold t          -> toMAlonzoType t  -- F (Fix F)
  H.Unfold t        -> M.C_Fix_46 (toMAlonzoType t)
  H.Compose _ f     -> getInputType f
  H.Pair f _        -> getInputType f
  H.Case f _        -> M.C__'43'__40 (getInputType f) M.C_Unit_34  -- Approximation
  H.Curry _ f       -> getInputType f  -- Approximation
  _                 -> M.C_Unit_34  -- Fallback

-- | Get output type of an IR expression
getOutputType :: H.IR -> M.T_Type_32
getOutputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a _         -> toMAlonzoType a
  H.Snd _ b         -> toMAlonzoType b
  H.Inl a b         -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.Inr a b         -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.Terminal _      -> M.C_Unit_34
  H.Initial t       -> toMAlonzoType t
  H.Apply _ b       -> toMAlonzoType b
  H.Fold t          -> M.C_Fix_46 (toMAlonzoType t)
  H.Unfold t        -> toMAlonzoType t  -- F (Fix F)
  H.Compose g _     -> getOutputType g
  H.Pair f g        -> M.C__'42'__38 (getOutputType f) (getOutputType g)
  H.Case f _        -> getOutputType f
  H.Curry _ f       -> getOutputType f  -- Approximation
  _                 -> M.C_Unit_34  -- Fallback

-- | Get middle type for composition (output of f, input of g)
getMiddleType :: H.IR -> H.IR -> M.T_Type_32
getMiddleType _ f = getOutputType f

