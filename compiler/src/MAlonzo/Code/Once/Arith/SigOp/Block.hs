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

module MAlonzo.Code.Once.Arith.SigOp.Block where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Arith.SigOp.Block.show-side
d_show'45'side_8 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'side_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe ("F" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe ("S" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-path
d_show'45'path_10 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'path_10 v0
  = case coe v0 of
      [] -> coe ("Z" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_show'45'side_8 (coe v1)) (d_show'45'path_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-zlit
d_show'45'zlit_16 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'zlit_16 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
            ("_" :: Data.Text.Text)
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("n" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (subInt (coe (0 :: Integer)) (coe v0)))
                ("_" :: Data.Text.Text))
-- Once.Arith.SigOp.Block.show-dlit
d_show'45'dlit_22 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'dlit_22 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_show'45'zlit_16
         (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.Nat.Show.d_show_56
            (MAlonzo.Code.Once.Spec.Float.Decimal.d_exp10_16 (coe v0)))
         ("_" :: Data.Text.Text))
-- Once.Arith.SigOp.Block.show-arith-ir
d_show'45'arith'45'ir_30 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'arith'45'ir_30 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("L" :: Data.Text.Text) (d_show'45'zlit_16 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("F" :: Data.Text.Text) (d_show'45'dlit_22 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("I" :: Data.Text.Text)
                    (d_show'45'path_10
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Shape.du_'8970'_'8971''7486'_114
                          (coe v0) (coe v4)))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("J" :: Data.Text.Text)
                    (d_show'45'path_10
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Shape.du_'8970'_'8971''7486'_114
                          (coe v0) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("A" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v4))
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v5)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("B" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v4))
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v5)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("M" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v4))
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v5)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("D" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v4))
                (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v5)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("R" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_show'45'arith'45'ir_30
                   (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3))
                (d_show'45'arith'45'ir_30
                   (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("G" :: Data.Text.Text)
             (d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("C" :: Data.Text.Text)
             (d_show'45'arith'45'ir_30
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("K" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'cmp_74 (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_show'45'arith'45'ir_30
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v4))
                   (d_show'45'arith'45'ir_30
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block._.show-cmp
d_show'45'cmp_74 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'cmp_74 ~v0 ~v1 ~v2 ~v3 v4 = du_show'45'cmp_74 v4
du_show'45'cmp_74 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'cmp_74 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12
        -> coe ("2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14
        -> coe ("3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16
        -> coe ("4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18
        -> coe ("5" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-digest
d_block'45'digest_80 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'digest_80 v0 v1 v2
  = coe d_show'45'arith'45'ir_30 (coe v0) (coe v1) (coe v2)
-- Once.Arith.SigOp.Block.block-name
d_block'45'name_88 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'name_88 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text)
      (d_block'45'digest_80 (coe v0) (coe v1) (coe v2))
-- Once.Arith.SigOp.Block.shape-as-type-base
d_shape'45'as'45'type'45'base_94 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_shape'45'as'45'type'45'base_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
             (d_shape'45'as'45'type'45'base_94 (coe v1))
             (d_shape'45'as'45'type'45'base_94 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.numtype-as-type-base
d_numtype'45'as'45'type'45'base_102 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_numtype'45'as'45'type'45'base_102 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-info
d_block'45'info_108 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_block'45'info_108 v0 v1 v2
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe d_block'45'name_88 (coe v0) (coe v1) (coe v2)))
      (coe MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v0 v1 v2)
      (coe d_shape'45'as'45'type'45'base_94 (coe v0))
      (coe d_numtype'45'as'45'type'45'base_102 (coe v1))
