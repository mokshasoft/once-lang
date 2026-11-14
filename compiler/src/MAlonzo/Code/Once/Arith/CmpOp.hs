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

module MAlonzo.Code.Once.Arith.CmpOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Encoding
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Word

-- Once.Arith.CmpOp.CmpOp
d_CmpOp_6 = ()
data T_CmpOp_6
  = C_c'45'lt_8 | C_c'45'le_10 | C_c'45'gt_12 | C_c'45'ge_14 |
    C_c'45'eq_16 | C_c'45'ne_18
-- Once.Arith.CmpOp.cmp-word
d_cmp'45'word_22 ::
  Integer -> T_CmpOp_6 -> Integer -> Integer -> Bool
d_cmp'45'word_22 v0 v1 v2 v3
  = case coe v1 of
      C_c'45'lt_8
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe v0) (coe v2)
             (coe v3)
      C_c'45'le_10
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe v0) (coe v3)
                (coe v2))
      C_c'45'gt_12
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe v0) (coe v3)
             (coe v2)
      C_c'45'ge_14
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe v0) (coe v2)
                (coe v3))
      C_c'45'eq_16
        -> coe
             MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82 (coe v2) (coe v3)
      C_c'45'ne_18
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82 (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.CmpOp.cmp-bit
d_cmp'45'bit_62 ::
  Integer -> T_CmpOp_6 -> Integer -> Integer -> Integer
d_cmp'45'bit_62 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_cmp'45'word_22 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe (1 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.CmpOp.FCmpOp
d_FCmpOp_72 = ()
data T_FCmpOp_72
  = C_fcmp_76 MAlonzo.Code.Once.Spec.Theory.T_Theory_16
              MAlonzo.Code.Once.Spec.Theory.T_Has_104
              MAlonzo.Code.Once.Spec.Theory.T_Sym_38
-- Once.Arith.CmpOp.floatTarget
d_floatTarget_78 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6
d_floatTarget_78 v0
  = coe
      MAlonzo.Code.Once.Spec.Numerics.C_mkTargetNum_20
      (coe (1 :: Integer)) (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Arith.CmpOp.fcmp-word
d_fcmp'45'word_82 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FCmpOp_72 -> Integer -> Integer -> Bool
d_fcmp'45'word_82 v0 v1 v2 v3
  = case coe v1 of
      C_fcmp_76 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Theory.du_'10214'_'10215''8347'_292 (coe v6)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_structure_504
                (coe d_floatTarget_78 (coe v0)) (coe v5))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Spec.Float.Encoding.d_decode_142 (coe v0)
                   (coe v2))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Encoding.d_decode_142 (coe v0)
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.CmpOp.fcmp-bit
d_fcmp'45'bit_94 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FCmpOp_72 -> Integer -> Integer -> Integer
d_fcmp'45'bit_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_fcmp'45'word_82 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe (1 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.CmpOp.fcmp-word-at
d_fcmp'45'word'45'at_116 ::
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fcmp'45'word'45'at_116 = erased
