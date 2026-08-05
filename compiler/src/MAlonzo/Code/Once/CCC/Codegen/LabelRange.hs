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

module MAlonzo.Code.Once.CCC.Codegen.LabelRange where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.CCC.Codegen.LabelRange.label-of
d_label'45'of_8 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_label'45'of_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.cata-label-of
d_cata'45'label'45'of_12 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'label'45'of_12 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.cata-label-mono
d_cata'45'label'45'mono_24 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'label'45'mono_24 v0 ~v1 v2 ~v3
  = du_cata'45'label'45'mono_24 v0 v2
du_cata'45'label'45'mono_24 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'label'45'mono_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_20
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                         (coe addInt (coe (3 :: Integer)) (coe v1)))
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                            (coe addInt (coe (4 :: Integer)) (coe v1)))
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                            (coe addInt (coe (5 :: Integer)) (coe v1)))))))
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_24
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                      (coe addInt (coe (3 :: Integer)) (coe v1)))))
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_26 v2
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                   (coe addInt (coe (4 :: Integer)) (coe v1)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                   (coe
                      addInt
                      (coe
                         addInt (coe (4 :: Integer))
                         (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v2)))
                      (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.label-mono
d_label'45'mono_62 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_label'45'mono_62 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__30 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_label'45'mono_62 (coe v0) (coe v6) (coe v9) (coe v3) (coe v4))
             (coe
                d_label'45'mono_62 (coe v6) (coe v1) (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                (coe
                   d_label'45'of_8
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v6) (coe v3) (coe v4) (coe v9))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              d_label'45'mono_62 (coe v0) (coe v11) (coe v8)
                              (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4))
                           (coe
                              d_label'45'mono_62 (coe v0) (coe v12) (coe v9)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                    (coe v4) (coe v8)))
                              (coe
                                 d_label'45'of_8
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                    (coe v4) (coe v8))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              d_label'45'mono_62 (coe v0) (coe v11) (coe v8)
                              (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                           (coe
                              d_label'45'mono_62 (coe v0) (coe v12) (coe v9)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                    (coe v4) (coe v8)))
                              (coe
                                 d_label'45'of_8
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                    (coe v4) (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_inl_56 v7
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_inr_62 v7
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_case_70 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             d_label'45'mono_62 (coe v10) (coe v1) (coe v8) (coe v3)
                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                          (coe
                             d_label'45'mono_62 (coe v11) (coe v1) (coe v9)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v10) (coe v1) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                             (coe
                                d_label'45'of_8
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v10) (coe v1) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_curry_86 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                             (coe addInt (coe (1 :: Integer)) (coe v4)))
                          (coe
                             d_label'45'mono_62
                             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                             (coe v11) (coe v8) (coe (0 :: Integer))
                             (coe addInt (coe (2 :: Integer)) (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_In_96 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_label'45'mono_62
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                       (coe v1) (coe v8) (coe v3) (coe v4))
                    (coe
                       du_cata'45'label'45'mono_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'strategy_48
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                       (coe
                          d_label'45'of_8
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                             (coe v1) (coe v3) (coe v4) (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v6 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Out_116 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Hylo_134 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Fuse_142 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_const_148 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_SigOp_154 v5 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
