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

module MAlonzo.Code.Once.Arith.Machine.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.Machine.IR.MArithIR
d_MArithIR_10 a0 = ()
data T_MArithIR_10
  = C_alit_14 Integer |
    C_ainput_16 [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] |
    C_aadd_18 T_MArithIR_10 T_MArithIR_10 |
    C_asub_20 T_MArithIR_10 T_MArithIR_10 |
    C_amul_22 T_MArithIR_10 T_MArithIR_10 |
    C_adiv_24 T_MArithIR_10 T_MArithIR_10 |
    C_amod_26 T_MArithIR_10 T_MArithIR_10 | C_aneg_28 T_MArithIR_10
-- Once.Arith.Machine.IR.divℤ
d_divℤ_30 :: Integer -> Integer -> Integer
d_divℤ_30 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.d__'9667'__238
            (coe
               MAlonzo.Code.Data.Sign.Base.d__'42'__14
               (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
               (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10))
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'47'__318
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe v1))
      _ -> coe
             MAlonzo.Code.Data.Integer.Base.d__'9667'__238
             (coe
                MAlonzo.Code.Data.Sign.Base.d__'42'__14
                (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
                (coe MAlonzo.Code.Data.Sign.Base.C_'45'_8))
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'47'__318
                (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                (coe subInt (coe (0 :: Integer)) (coe v1)))
-- Once.Arith.Machine.IR.modℤ
d_modℤ_32 :: Integer -> Integer -> Integer
d_modℤ_32 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.d__'9667'__238
            (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'37'__330
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe v1))
      _ -> coe
             MAlonzo.Code.Data.Integer.Base.d__'9667'__238
             (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'37'__330
                (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                (coe subInt (coe (0 :: Integer)) (coe v1)))
-- Once.Arith.Machine.IR.eval-arith
d_eval'45'arith_56 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  T_MArithIR_10 -> AgdaAny -> Integer
d_eval'45'arith_56 v0 v1 v2
  = case coe v1 of
      C_alit_14 v3 -> coe v3
      C_ainput_16 v3
        -> let v4
                 = MAlonzo.Code.Once.Arith.Machine.Shape.d_project_32
                     (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v5
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_aadd_18 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__284
             (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_56 (coe v0) (coe v4) (coe v2))
      C_asub_20 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'45'__302
             (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_56 (coe v0) (coe v4) (coe v2))
      C_amul_22 v3 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'42'__316
             (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_56 (coe v0) (coe v4) (coe v2))
      C_adiv_24 v3 v4
        -> coe
             d_divℤ_30 (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_56 (coe v0) (coe v4) (coe v2))
      C_amod_26 v3 v4
        -> coe
             d_modℤ_32 (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_56 (coe v0) (coe v4) (coe v2))
      C_aneg_28 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.d_'45'__260
             (coe d_eval'45'arith_56 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.shape-as-type
d_shape'45'as'45'type_120 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_shape'45'as'45'type_120 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Type.C_Unit_122
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Type.C_Int_136
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_14 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__126
             (coe d_shape'45'as'45'type_120 (coe v1))
             (coe d_shape'45'as'45'type_120 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock
d_ArithBlock_126 = ()
data T_ArithBlock_126
  = C_mk'45'block_136 MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
                      T_MArithIR_10
-- Once.Arith.Machine.IR.ArithBlock.block-shape
d_block'45'shape_132 ::
  T_ArithBlock_126 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_block'45'shape_132 v0
  = case coe v0 of
      C_mk'45'block_136 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-body
d_block'45'body_134 :: T_ArithBlock_126 -> T_MArithIR_10
d_block'45'body_134 v0
  = case coe v0 of
      C_mk'45'block_136 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.leaf-count
d_leaf'45'count_140 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  T_MArithIR_10 -> Integer
d_leaf'45'count_140 ~v0 v1 = du_leaf'45'count_140 v1
du_leaf'45'count_140 :: T_MArithIR_10 -> Integer
du_leaf'45'count_140 v0
  = case coe v0 of
      C_alit_14 v1 -> coe (1 :: Integer)
      C_ainput_16 v1 -> coe (1 :: Integer)
      C_aadd_18 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_140 (coe v1))
             (coe du_leaf'45'count_140 (coe v2))
      C_asub_20 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_140 (coe v1))
             (coe du_leaf'45'count_140 (coe v2))
      C_amul_22 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_140 (coe v1))
             (coe du_leaf'45'count_140 (coe v2))
      C_adiv_24 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_140 (coe v1))
             (coe du_leaf'45'count_140 (coe v2))
      C_amod_26 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_140 (coe v1))
             (coe du_leaf'45'count_140 (coe v2))
      C_aneg_28 v1 -> coe du_leaf'45'count_140 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
