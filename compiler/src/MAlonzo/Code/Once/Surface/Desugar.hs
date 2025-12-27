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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Desugar.prim
d_prim_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Surface.Desugar.prim"
-- Once.Surface.Desugar.desugar
d_desugar_16 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_4
d_desugar_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.IR.C_id_10
        -> coe MAlonzo.Code.Once.IR.C_id_8
      MAlonzo.Code.Once.Surface.IR.C__'8728'__18 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__16 v4
             (d_desugar_16 (coe v4) (coe v1) (coe v6))
             (d_desugar_16 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.Surface.IR.C_fst_24
        -> coe MAlonzo.Code.Once.IR.C_fst_22
      MAlonzo.Code.Once.Surface.IR.C_snd_30
        -> coe MAlonzo.Code.Once.IR.C_snd_28
      MAlonzo.Code.Once.Surface.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (d_desugar_16 (coe v0) (coe v8) (coe v6))
                    (d_desugar_16 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_inl_44
        -> coe MAlonzo.Code.Once.IR.C_inl_42
      MAlonzo.Code.Once.Surface.IR.C_inr_50
        -> coe MAlonzo.Code.Once.IR.C_inr_48
      MAlonzo.Code.Once.Surface.IR.C_'91'_'44'_'93'_58 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                    (d_desugar_16 (coe v8) (coe v1) (coe v6))
                    (d_desugar_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_terminal_62
        -> coe MAlonzo.Code.Once.IR.C_terminal_60
      MAlonzo.Code.Once.Surface.IR.C_initial_66
        -> coe MAlonzo.Code.Once.IR.C_initial_64
      MAlonzo.Code.Once.Surface.IR.C_curry_74 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_72
                    (d_desugar_16
                       (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.IR.C_apply_80
        -> coe MAlonzo.Code.Once.IR.C_apply_78
      MAlonzo.Code.Once.Surface.IR.C_fold_84
        -> coe MAlonzo.Code.Once.IR.C_fold_82
      MAlonzo.Code.Once.Surface.IR.C_unfold_88
        -> coe MAlonzo.Code.Once.IR.C_unfold_86
      MAlonzo.Code.Once.Surface.IR.C_arr_94
        -> coe MAlonzo.Code.Once.IR.C_arr_92
      MAlonzo.Code.Once.Surface.IR.C_Let_102 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__16
             (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v4))
             (d_desugar_16
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v4)) (coe v1)
                (coe v7))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe MAlonzo.Code.Once.IR.C_id_8)
                (d_desugar_16 (coe v0) (coe v4) (coe v6)))
      MAlonzo.Code.Once.Surface.IR.C_Prim_108 v5
        -> coe d_prim_10 v0 v1 v5
      _ -> MAlonzo.RTE.mazUnreachableError
