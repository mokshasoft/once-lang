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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Desugar.prim-desugar
d_prim'45'desugar_10 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_prim'45'desugar_10 ~v0 ~v1 = du_prim'45'desugar_10
du_prim'45'desugar_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_prim'45'desugar_10 = coe MAlonzo.Code.Once.CCC.IR.C_Prim_156
-- Once.Surface.Desugar.desugar
d_desugar_16 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_desugar_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_16
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v4
             (d_desugar_16 (coe v4) (coe v1) (coe v6))
             (d_desugar_16 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_38
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_44
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__52 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (d_desugar_16 (coe v0) (coe v8) (coe v6))
                    (d_desugar_16 (coe v0) (coe v9) (coe v7))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_inl_50
             (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_inr_56
             (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__54 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_64
                    (d_desugar_16 (coe v8) (coe v1) (coe v6))
                    (d_desugar_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_72
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_82
                    (d_desugar_16
                       (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v0) (coe v7)) (coe v9)
                       (coe v6))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_90
      MAlonzo.Code.Once.Surface.IR.C_arr_86
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_98
      MAlonzo.Code.Once.Surface.IR.C_Let_94 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v0) (coe v4))
             (d_desugar_16
                (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v0) (coe v4)) (coe v1)
                (coe v7))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe MAlonzo.Code.Once.CCC.IR.C_id_16)
                (d_desugar_16 (coe v0) (coe v4) (coe v6))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.IR.C_Prim_100 v5
        -> coe du_prim'45'desugar_10 v5
      _ -> MAlonzo.RTE.mazUnreachableError
