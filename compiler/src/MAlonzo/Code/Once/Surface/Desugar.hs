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

module MAlonzo.Code.Once.Surface.Desugar where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Desugar.prim-desugar
d_prim'45'desugar_10 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_prim'45'desugar_10 ~v0 ~v1 = du_prim'45'desugar_10
du_prim'45'desugar_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
du_prim'45'desugar_10 = coe MAlonzo.Code.Once.IR.C_Prim_108
-- Once.Surface.Desugar.desugar
d_desugar_16 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_desugar_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.IR.C_id_14
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22 v4
             (d_desugar_16 (coe v4) (coe v1) (coe v6))
             (d_desugar_16 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.IR.C_fst_28
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.IR.C_snd_34
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                    (d_desugar_16 (coe v0) (coe v8) (coe v6))
                    (d_desugar_16 (coe v0) (coe v9) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_Heap_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe
             MAlonzo.Code.Once.IR.C_inl_48 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe
             MAlonzo.Code.Once.IR.C_inr_54 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62
                    (d_desugar_16 (coe v8) (coe v1) (coe v6))
                    (d_desugar_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.IR.C_terminal_66
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.IR.C_initial_70
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_80
                    (d_desugar_16
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v7)) (coe v9)
                       (coe v6))
                    (coe MAlonzo.Code.Once.IR.C_Heap_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.IR.C_apply_88
      MAlonzo.Code.Once.Surface.IR.C_fold_84
        -> coe MAlonzo.Code.Once.IR.C_fold_92
      MAlonzo.Code.Once.Surface.IR.C_unfold_88
        -> coe MAlonzo.Code.Once.IR.C_unfold_96
      MAlonzo.Code.Once.Surface.IR.C_arr_94
        -> coe MAlonzo.Code.Once.IR.C_arr_102
      MAlonzo.Code.Once.Surface.IR.C_Let_102 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v4))
             (d_desugar_16
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v4)) (coe v1)
                (coe v7))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe MAlonzo.Code.Once.IR.C_id_14)
                (d_desugar_16 (coe v0) (coe v4) (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.IR.C_Prim_108 v5
        -> coe du_prim'45'desugar_10 v5
      _ -> MAlonzo.RTE.mazUnreachableError
