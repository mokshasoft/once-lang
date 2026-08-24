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

module MAlonzo.Code.Once.IRLits where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.IRLits.constLits
d_constLits_8 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 -> AgdaAny -> [Integer]
d_constLits_8 ~v0 v1 v2 = du_constLits_8 v1 v2
du_constLits_8 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 -> AgdaAny -> [Integer]
du_constLits_8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRLits.irIntLits
d_irIntLits_16 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> [Integer]
d_irIntLits_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_irIntLits_16 (coe v4) (coe v1) (coe v6))
             (coe d_irIntLits_16 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_irIntLits_16 (coe v0) (coe v9) (coe v6))
                    (coe d_irIntLits_16 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_inl_56 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_inr_62 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_irIntLits_16 (coe v8) (coe v1) (coe v6))
                    (coe d_irIntLits_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_curry_86 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
               -> coe
                    d_irIntLits_16
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8)) (coe v9)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_In_96 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    d_irIntLits_16
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v1))
                    (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    d_irIntLits_16
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                    (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_116 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_Ana_126 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    d_irIntLits_16 (coe v0)
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_134 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_irIntLits_16
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_ntIntLits_22 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_142 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_irIntLits_16
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_ntIntLits_22 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_const_148 v4 v5
        -> coe du_constLits_8 (coe v4) (coe v5)
      MAlonzo.Code.Once.IR.C_SigOp_154 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRLits.ntIntLits
d_ntIntLits_22 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> [Integer]
d_ntIntLits_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_156
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.IR.C_ntK_162 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe d_irIntLits_16 (coe v6) (coe v7) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_170 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe d_ntIntLits_22 (coe v7) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_178 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe d_ntIntLits_22 (coe v8) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_186 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_ntIntLits_22 (coe v8) (coe v1) (coe v6))
                    (coe d_ntIntLits_22 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_194 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe d_ntIntLits_22 (coe v0) (coe v7) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_202 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe d_ntIntLits_22 (coe v0) (coe v8) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_210 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_ntIntLits_22 (coe v0) (coe v8) (coe v6))
                    (coe d_ntIntLits_22 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
