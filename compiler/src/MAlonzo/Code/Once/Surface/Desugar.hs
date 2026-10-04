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
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Desugar.sigOp-desugar
d_sigOp'45'desugar_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_sigOp'45'desugar_10 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_130 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Builders.du_generic'45'info_350
         (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v4)) v2 v3)
-- Once.Surface.Desugar.desugar
d_desugar_22 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_desugar_22 v0 v1 ~v2 v3 = du_desugar_22 v0 v1 v3
du_desugar_22 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_desugar_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
             (coe du_desugar_22 (coe v4) (coe v1) (coe v6))
             (coe du_desugar_22 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__124 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe du_desugar_22 (coe v0) (coe v8) (coe v6))
                    (coe du_desugar_22 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe MAlonzo.Code.Once.IR.C_inl_54
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe MAlonzo.Code.Once.IR.C_inr_60
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68
                    (coe du_desugar_22 (coe v8) (coe v1) (coe v6))
                    (coe du_desugar_22 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_84
                    (coe
                       du_desugar_22
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v0) (coe v7))
                       (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.IR.C_apply_90
      MAlonzo.Code.Once.Surface.IR.C_arr_86
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Surface.IR.C_Let_94 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v0) (coe v4)))
             (coe
                du_desugar_22
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v0) (coe v4))
                (coe v1) (coe v7))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe MAlonzo.Code.Once.IR.C_id_20)
                (coe du_desugar_22 (coe v0) (coe v4) (coe v6)))
      MAlonzo.Code.Once.Surface.IR.C_SigOp_100 v5 v6 v7
        -> coe
             d_sigOp'45'desugar_10 (coe v0) (coe v1) (coe v6) (coe v7) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Desugar.desugar-default
d_desugar'45'default_82 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_desugar'45'default_82 v0 v1 = coe du_desugar_22 (coe v0) (coe v1)
