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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Desugar.sigOp-desugar
d_sigOp'45'desugar_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_sigOp'45'desugar_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_172
      (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_202
         (coe v0) (coe v1) (coe v2))
-- Once.Surface.Desugar.desugar
d_desugar_18 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_desugar_18 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_28
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__36 v5
             (d_desugar_18 (coe v5) (coe v1) (coe v2) (coe v7))
             (d_desugar_18 (coe v0) (coe v5) (coe v2) (coe v8))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_50
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_56
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_44
                    (d_desugar_18 (coe v0) (coe v9) (coe v2) (coe v7))
                    (d_desugar_18 (coe v0) (coe v10) (coe v2) (coe v8)) v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe MAlonzo.Code.Once.CCC.IR.C_inl_62 v2
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe MAlonzo.Code.Once.CCC.IR.C_inr_68 v2
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_76
                    (d_desugar_18 (coe v9) (coe v1) (coe v2) (coe v7))
                    (d_desugar_18 (coe v10) (coe v1) (coe v2) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_80
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_84
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_94
                    (d_desugar_18
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v8))
                       (coe v10) (coe v2) (coe v7))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_102
      MAlonzo.Code.Once.Surface.IR.C_arr_86
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_110
      MAlonzo.Code.Once.Surface.IR.C_Let_94 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__36
             (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v5))
             (d_desugar_18
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v5))
                (coe v1) (coe v2) (coe v8))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_44
                (coe MAlonzo.Code.Once.CCC.IR.C_id_28)
                (d_desugar_18 (coe v0) (coe v5) (coe v2) (coe v7)) v2)
      MAlonzo.Code.Once.Surface.IR.C_SigOp_100 v6
        -> coe d_sigOp'45'desugar_10 (coe v0) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Desugar.desugar-default
d_desugar'45'default_74 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_desugar'45'default_74 v0 v1
  = coe
      d_desugar_18 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
