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
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.Machine.IR.MArithIR
d_MArithIR_10 a0 a1 = ()
data T_MArithIR_10
  = C_alit_14 Integer |
    C_aflit_16 MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 |
    C_ainput_20 [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] |
    C_aadd_24 T_MArithIR_10 T_MArithIR_10 |
    C_asub_28 T_MArithIR_10 T_MArithIR_10 |
    C_amul_32 T_MArithIR_10 T_MArithIR_10 |
    C_adiv_34 T_MArithIR_10 T_MArithIR_10 |
    C_amod_36 T_MArithIR_10 T_MArithIR_10 | C_aneg_40 T_MArithIR_10 |
    C_ai2f_42 T_MArithIR_10
-- Once.Arith.Machine.IR.divℤ
d_divℤ_44 :: Integer -> Integer -> Integer
d_divℤ_44 v0 v1
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
d_modℤ_46 :: Integer -> Integer -> Integer
d_modℤ_46 v0 v1
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
d_eval'45'arith_70 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  T_MArithIR_10 -> AgdaAny -> Integer
d_eval'45'arith_70 v0 v1 v2
  = case coe v1 of
      C_alit_14 v3 -> coe v3
      C_ainput_20 v4
        -> let v5
                 = MAlonzo.Code.Once.Arith.Machine.Shape.d_project_34
                     (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6 -> coe v6
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_aadd_24 v4 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__284
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
             (coe d_eval'45'arith_70 (coe v0) (coe v5) (coe v2))
      C_asub_28 v4 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'45'__302
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
             (coe d_eval'45'arith_70 (coe v0) (coe v5) (coe v2))
      C_amul_32 v4 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'42'__316
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
             (coe d_eval'45'arith_70 (coe v0) (coe v5) (coe v2))
      C_adiv_34 v3 v4
        -> coe
             d_divℤ_44 (coe d_eval'45'arith_70 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
      C_amod_36 v3 v4
        -> coe
             d_modℤ_46 (coe d_eval'45'arith_70 (coe v0) (coe v3) (coe v2))
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
      C_aneg_40 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.d_'45'__260
             (coe d_eval'45'arith_70 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.shape-as-type
d_shape'45'as'45'type_134 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_shape'45'as'45'type_134 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Type.C_Unit_122
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Type.C_Int_136
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14
        -> coe MAlonzo.Code.Once.Type.C_Float_138
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__126
             (coe d_shape'45'as'45'type_134 (coe v1))
             (coe d_shape'45'as'45'type_134 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.numtype-as-type
d_numtype'45'as'45'type_140 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_numtype'45'as'45'type_140 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe MAlonzo.Code.Once.Type.C_Int_136
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe MAlonzo.Code.Once.Type.C_Float_138
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock
d_ArithBlock_142 = ()
data T_ArithBlock_142
  = C_mk'45'block_156 MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
                      MAlonzo.Code.Once.Arith.Type.T_NumType_6 T_MArithIR_10
-- Once.Arith.Machine.IR.ArithBlock.block-shape
d_block'45'shape_150 ::
  T_ArithBlock_142 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
d_block'45'shape_150 v0
  = case coe v0 of
      C_mk'45'block_156 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-kind
d_block'45'kind_152 ::
  T_ArithBlock_142 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
d_block'45'kind_152 v0
  = case coe v0 of
      C_mk'45'block_156 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.ArithBlock.block-body
d_block'45'body_154 :: T_ArithBlock_142 -> T_MArithIR_10
d_block'45'body_154 v0
  = case coe v0 of
      C_mk'45'block_156 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.IR.leaf-count
d_leaf'45'count_162 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  T_MArithIR_10 -> Integer
d_leaf'45'count_162 ~v0 ~v1 v2 = du_leaf'45'count_162 v2
du_leaf'45'count_162 :: T_MArithIR_10 -> Integer
du_leaf'45'count_162 v0
  = case coe v0 of
      C_alit_14 v1 -> coe (1 :: Integer)
      C_aflit_16 v1 -> coe (1 :: Integer)
      C_ainput_20 v2 -> coe (1 :: Integer)
      C_aadd_24 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_162 (coe v2))
             (coe du_leaf'45'count_162 (coe v3))
      C_asub_28 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_162 (coe v2))
             (coe du_leaf'45'count_162 (coe v3))
      C_amul_32 v2 v3
        -> coe
             addInt (coe du_leaf'45'count_162 (coe v2))
             (coe du_leaf'45'count_162 (coe v3))
      C_adiv_34 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_162 (coe v1))
             (coe du_leaf'45'count_162 (coe v2))
      C_amod_36 v1 v2
        -> coe
             addInt (coe du_leaf'45'count_162 (coe v1))
             (coe du_leaf'45'count_162 (coe v2))
      C_aneg_40 v2 -> coe du_leaf'45'count_162 (coe v2)
      C_ai2f_42 v1 -> coe du_leaf'45'count_162 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
