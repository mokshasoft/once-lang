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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_sigOp'45'desugar_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_418
      (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
         (coe v0) (coe v1) (coe v2))
-- Once.Surface.Desugar.desugar
d_desugar_18 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_desugar_18 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_274
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__282 v4
             (d_desugar_18 (coe v4) (coe v1) (coe v6))
             (d_desugar_18 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_296
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_302
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_290
                    (d_desugar_18 (coe v0) (coe v8) (coe v6))
                    (d_desugar_18 (coe v0) (coe v9) (coe v7))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_inl_308
             (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_inr_314
             (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_322
                    (d_desugar_18 (coe v8) (coe v1) (coe v6))
                    (d_desugar_18 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_326
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_330
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_340
                    (d_desugar_18
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v7))
                       (coe v9) (coe v6))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_348
      MAlonzo.Code.Once.Surface.IR.C_arr_86
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_356
      MAlonzo.Code.Once.Surface.IR.C_Let_94 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__282
             (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v4))
             (d_desugar_18
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v4))
                (coe v1) (coe v7))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_290
                (coe MAlonzo.Code.Once.CCC.IR.C_id_274)
                (d_desugar_18 (coe v0) (coe v4) (coe v6))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262))
      MAlonzo.Code.Once.Surface.IR.C_SigOp_100 v5
        -> coe d_sigOp'45'desugar_10 (coe v0) (coe v1) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
