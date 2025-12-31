{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.TypeCheck.Sound where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Infer
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Sound.WellTyped
d_WellTyped_6 a0 a1 a2 = ()
data T_WellTyped_6
  = C_T'45'Var_18 MAlonzo.Code.Once.Type.T_Quantity_4 Integer |
    C_T'45'Gen_30 Integer Integer |
    C_T'45'App_42 MAlonzo.Code.Once.Type.T_Type_32 T_WellTyped_6
                  T_WellTyped_6 |
    C_T'45'Lam_54 T_WellTyped_6 |
    C_T'45'Let_68 MAlonzo.Code.Once.Type.T_Type_32 T_WellTyped_6
                  T_WellTyped_6 |
    C_T'45'Pair_80 T_WellTyped_6 T_WellTyped_6 |
    C_T'45'Case_100 MAlonzo.Code.Once.Type.T_Type_32
                    MAlonzo.Code.Once.Type.T_Type_32 T_WellTyped_6 T_WellTyped_6
                    T_WellTyped_6 |
    C_T'45'Unit_104 | C_T'45'Int_110 | C_T'45'Str_116 |
    C_T'45'Annot_124 T_WellTyped_6 |
    C_T'45'BinArith_134 T_WellTyped_6 T_WellTyped_6 |
    C_T'45'BinCmp_144 T_WellTyped_6 T_WellTyped_6 |
    C_T'45'Neg_150 T_WellTyped_6
-- Once.TypeCheck.Sound.applySubst-empty
d_applySubst'45'empty_154 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applySubst'45'empty_154 = erased
-- Once.TypeCheck.Sound.unify-sound
d_unify'45'sound_188
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Sound.unify-sound"
-- Once.TypeCheck.Sound.Soundness
d_Soundness_190 :: ()
d_Soundness_190 = erased
-- Once.TypeCheck.Sound.soundness
d_soundness_204
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Sound.soundness"
-- Once.TypeCheck.Sound.Closed
d_Closed_206 a0 = ()
data T_Closed_206
  = C_closed'45'unit_208 | C_closed'45'void_210 |
    C_closed'45'int_212 | C_closed'45'float_214 | C_closed'45'str_216 |
    C_closed'45'buffer_218 |
    C_closed'45'prod_224 T_Closed_206 T_Closed_206 |
    C_closed'45'sum_230 T_Closed_206 T_Closed_206 |
    C_closed'45'arrow_236 T_Closed_206 T_Closed_206 |
    C_closed'45'eff_242 T_Closed_206 T_Closed_206 |
    C_closed'45'fix_246 T_Closed_206
-- Once.TypeCheck.Sound.applySubst-closed
d_applySubst'45'closed_252
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Sound.applySubst-closed"
-- Once.TypeCheck.Sound.Decidable
d_Decidable_254 :: ()
d_Decidable_254 = erased
-- Once.TypeCheck.Sound.decidable
d_decidable_264 ::
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decidable_264 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Infer.d_infer_148 (coe v0) (coe v1)
         (coe v2))
      erased
