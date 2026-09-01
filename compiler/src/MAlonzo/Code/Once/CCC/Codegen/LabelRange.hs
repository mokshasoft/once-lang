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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.LabelRange._.CataStrategy
d_CataStrategy_12 a0 = ()
-- Once.CCC.Codegen.LabelRange._.cata-dispatch
d_cata'45'dispatch_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
      (coe v0)
-- Once.CCC.Codegen.LabelRange._.ir-to-trace'
d_ir'45'to'45'trace''_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
      (coe v0)
-- Once.CCC.Codegen.LabelRange.label-of
d_label'45'of_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_label'45'of_40 ~v0 v1 = du_label'45'of_40 v1
du_label'45'of_40 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_label'45'of_40 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.cata-label-of
d_cata'45'label'45'of_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'label'45'of_44 ~v0 v1 = du_cata'45'label'45'of_44 v1
du_cata'45'label'45'of_44 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'label'45'of_44 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.cata-label-mono
d_cata'45'label'45'mono_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'label'45'mono_58 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_cata'45'label'45'mono_58 v1 v4
du_cata'45'label'45'mono_58 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'label'45'mono_58 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v1)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
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
                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                               (coe addInt (coe (5 :: Integer)) (coe v1)))
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                  (coe addInt (coe (6 :: Integer)) (coe v1)))
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                  (coe addInt (coe (7 :: Integer)) (coe v1)))))))))
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
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
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v2
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
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                      (coe
                         addInt
                         (coe
                            addInt (coe (4 :: Integer))
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v2)))
                         (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                      (coe
                         addInt
                         (coe
                            addInt
                            (coe
                               addInt (coe (4 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v2)))
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v2)))
                         (coe v1)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelRange.label-mono
d_label'45'mono_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_label'45'mono_104 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_label'45'mono_104 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                (coe v5))
             (coe
                d_label'45'mono_104 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_label'45'of_40
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              d_label'45'mono_104 (coe v0) (coe v1) (coe v12) (coe v9)
                              (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5))
                           (coe
                              d_label'45'mono_104 (coe v0) (coe v1) (coe v13) (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_label'45'of_40
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5) (coe v9))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              d_label'45'mono_104 (coe v0) (coe v1) (coe v12) (coe v9)
                              (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                           (coe
                              d_label'45'mono_104 (coe v0) (coe v1) (coe v13) (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_label'45'of_40
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5))
      MAlonzo.Code.Once.IR.C_inr_62 v8
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5))
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v5))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe addInt (coe (1 :: Integer)) (coe v5)))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             d_label'45'mono_104 (coe v0) (coe v11) (coe v2) (coe v9) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)))
                          (coe
                             d_label'45'mono_104 (coe v0) (coe v12) (coe v2) (coe v10)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                du_label'45'of_40
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v5))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                             (coe addInt (coe (1 :: Integer)) (coe v5)))
                          (coe
                             d_label'45'mono_104 (coe v0)
                             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                             (coe v12) (coe v9) (coe (0 :: Integer))
                             (coe addInt (coe (2 :: Integer)) (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_Cata_108 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              d_label'45'mono_104 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v13)
                                    (coe v2)))
                              (coe v2) (coe v10) (coe (0 :: Integer)) (coe v5))
                           (coe
                              du_cata'45'label'45'mono_58
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v13)))
                              (coe
                                 du_label'45'of_40
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v13)
                                          (coe v2)))
                                    (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_Out_118 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_Ana_128 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      MAlonzo.Code.Once.IR.C_const_150 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5))
      MAlonzo.Code.Once.IR.C_SigOp_156 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
