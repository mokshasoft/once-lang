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

module MAlonzo.Code.Once.CCC.Codegen.SlotBudget where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotSeg
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.SlotBudget._.CataStrategy
d_CataStrategy_12 a0 = ()
-- Once.CCC.Codegen.SlotBudget._.cata-body
d_cata'45'body_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_cata'45'br'45'I'8321'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₂
d_cata'45'br'45'I'8322'_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_cata'45'br'45'I'8322'_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-dispatch
d_cata'45'dispatch_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.fsize
d_fsize_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
d_fsize_32 ~v0 = du_fsize_32
du_fsize_32 :: MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
du_fsize_32
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget
d_ir'45'stack'45'budget_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_34 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_824
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace
d_ir'45'to'45'trace_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_ir'45'to'45'trace_38 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace'
d_ir'45'to'45'trace''_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_ir'45'to'45'trace'45'lab_42 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_882
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-unit
d_ir'45'to'45'unit_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2314
d_ir'45'to'45'unit_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_800
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.pop2
d_pop2_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_pop2_48 ~v0 = du_pop2_48
du_pop2_48 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_pop2_48
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_182
-- Once.CCC.Codegen.SlotBudget._.push2
d_push2_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_push2_50 ~v0 = du_push2_50
du_push2_50 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_push2_50
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
-- Once.CCC.Codegen.SlotBudget._.rebuild-walk
d_rebuild'45'walk_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_rebuild'45'walk_52 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.SlotBudget._.resuspend-layer
d_resuspend'45'layer_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_54 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.visit-walk
d_visit'45'walk_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_visit'45'walk_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.wrap-sum
d_wrap'45'sum_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_wrap'45'sum_66 ~v0 = du_wrap'45'sum_66
du_wrap'45'sum_66 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_wrap'45'sum_66
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_78 ~v0 v1 = du_budget'45'of_78 v1
du_budget'45'of_78 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_78 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_trace'45'of_82 ~v0 v1 = du_trace'45'of_82 v1
du_trace'45'of_82 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_trace'45'of_82 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-budget-of
d_cata'45'budget'45'of_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_86 ~v0 v1 = du_cata'45'budget'45'of_86 v1
du_cata'45'budget'45'of_86 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'budget'45'of_86 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_cata'45'trace'45'of_90 ~v0 v1 = du_cata'45'trace'45'of_90 v1
du_cata'45'trace'45'of_90 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_cata'45'trace'45'of_90 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_104 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_cata'45'mono_104 v1 v3
du_cata'45'mono_104 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_104 v0 v1
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
                            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                            (coe addInt (coe (5 :: Integer)) (coe v1)))))))
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v2
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                   (coe addInt (coe (7 :: Integer)) (coe v1)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                      (coe
                         addInt
                         (coe
                            addInt (coe (7 :: Integer))
                            (coe
                               mulInt (coe (4 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v2))))
                         (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                      (coe
                         addInt
                         (coe
                            addInt (coe (11 :: Integer))
                            (coe
                               mulInt (coe (4 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v2))))
                         (coe v1)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.frontier-mono
d_frontier'45'mono_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_150 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_150 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_frontier'45'mono_150 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   du_budget'45'of_78
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
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
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                (coe addInt (coe (2 :: Integer)) (coe v4)))
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                (coe addInt (coe (3 :: Integer)) (coe v4))))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          d_frontier'45'mono_150 (coe v0) (coe v1) (coe v11) (coe v9)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                       (coe
                          d_frontier'45'mono_150 (coe v0) (coe v1) (coe v12) (coe v10)
                          (coe
                             du_budget'45'of_78
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_frontier'45'mono_150 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_frontier'45'mono_150 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          du_budget'45'of_78
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_apply_90
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
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (2 :: Integer)) (coe v4))))
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           du_cata'45'mono_104
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v13)))
                           (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_Ana_120 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_const_124 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_SigOp_130 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Call_136 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.lt-refl
d_lt'45'refl_262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_262 ~v0 v1 = du_lt'45'refl_262 v1
du_lt'45'refl_262 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lt'45'refl_262 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_270 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'nat'45'layer'45'below_270 v4 v5
du_cata'45'nat'45'layer'45'below_270 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_270 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
            erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
                  erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
                              erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-body-below
d_cata'45'body'45'below_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'body'45'below_300 v0 v1 ~v2 v3 ~v4 v5 v6
  = du_cata'45'body'45'below_300 v0 v1 v3 v5 v6
du_cata'45'body'45'below_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
du_cata'45'body'45'below_300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'thunk_640
         (coe v1) (coe v3) (coe v4))
-- Once.CCC.Codegen.SlotBudget.cata-const-below
d_cata'45'const'45'below_320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'const'45'below_320 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe addInt (coe (2 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (1 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (2 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0) (coe v3)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (3 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v2)))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                  (coe addInt (coe (2 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (1 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe v2))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0) (coe v3)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (3 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v2)))
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_ev'60'b_348 (coe v2)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_k'60'b_346 (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_pr'60'b_350 (coe v2)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_ev'60'b_348 (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_cl'60'b_344 (coe v2)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                               (coe du_k'60'b_346 (coe v2)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                        (coe du_k'60'b_346 (coe v2))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                           (coe
                                                                              du_pr'60'b_350
                                                                              (coe v2))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                                 (coe
                                                                                    du_k'60'b_346
                                                                                    (coe v2))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                                       (coe
                                                                                          du_cl'60'b_344
                                                                                          (coe v2))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                                                (coe
                                                                                                   du_pr'60'b_350
                                                                                                   (coe
                                                                                                      v2))
                                                                                                erased)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))))))
      (coe
         du_cata'45'body'45'below_300 (coe v0)
         (coe
            du_cata'45'budget'45'of_86
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
               (coe v0)
               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22)
               (coe v1) (coe v2) (coe v3) (coe v4)))
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_338 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 = du_bnd_338 v2 v6 v7
du_bnd_338 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_338 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v0 (addInt (coe (1 :: Integer)) (coe v1)) (4 :: Integer) v2)
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_344 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_344 v2
du_cl'60'b_344 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_344 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
      (coe
         du_bnd_338 (coe v0) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_346 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_346 v2
du_k'60'b_346 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_346 v0
  = coe
      du_bnd_338 (coe v0) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_348 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_348 v2
du_ev'60'b_348 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_348 v0
  = coe
      du_bnd_338 (coe v0) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_350 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_350 v2
du_pr'60'b_350 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_350 v0
  = coe
      du_bnd_338 (coe v0) (coe (3 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe
                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                  (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))))
-- Once.CCC.Codegen.SlotBudget.cata-nat-below
d_cata'45'nat'45'below_382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'nat'45'below_382 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe addInt (coe (4 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (4 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (6 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                  (coe addInt (coe (4 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (4 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (6 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_412 (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                      (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0) (coe v3))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v3)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                            (coe (0 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                                                 (coe
                                                                                    (0 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v2)))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                   (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (3 :: Integer)) (coe v3)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                               (coe v0)
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v3)))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                               (coe (0 :: Integer)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                                           (coe (2 :: Integer)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (1 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v2)))
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
            (coe du_I'8321'_438 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                        (coe addInt (coe (5 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe addInt (coe (2 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                (coe addInt (coe (5 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_426 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                           (coe addInt (coe (4 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (5 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                             (coe (1 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (4 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (5 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                    (coe v2))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                (coe (1 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
                  (coe du_I'8322'_448 (coe v2)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (3 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                   (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (5 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                      (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_426 (coe v2)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (5 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (4 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                          (coe addInt (coe (5 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_458))
                     (coe
                        du_cata'45'body'45'below_300 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_86
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (7 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_398 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_398 v2
du_b_398 :: Integer -> Integer
du_b_398 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_400 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p'60'b_400 v2
du_p'60'b_400 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_400 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_402 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_s'60'b_402 v2
du_s'60'b_402 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_402 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_404 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_404 v2
du_cl'60'b_404 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_404 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_406 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_406 v2
du_k'60'b_406 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_406 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_408 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_408 v2
du_ev'60'b_408 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_408 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_410 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_410 v2
du_pr'60'b_410 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_410 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_412 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_412 v2
du_setup_412 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_412 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b_408 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b_406 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b_410 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b_408 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_cl'60'b_404 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                         (coe du_k'60'b_406 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_426 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_426 v2
du_call_426 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_426 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b_406 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b_410 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b_406 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b_404 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_pr'60'b_410 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_438 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_438 v2
du_I'8321'_438 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_438 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                               (coe du_p'60'b_400 (coe v0)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                     (coe du_s'60'b_402 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                                 (coe
                                                                                    du_p'60'b_400
                                                                                    (coe v0))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                                       (coe
                                                                                          du_s'60'b_402
                                                                                          (coe v0))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_448 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_448 v2
du_I'8322'_448 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_448 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_p'60'b_400 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_s'60'b_402 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_p'60'b_400 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_s'60'b_402 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_458
du_I'8323'_458 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_458
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.cata-linear-below
d_cata'45'linear'45'below_468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'linear'45'below_468 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe addInt (coe (8 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (8 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (4 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (7 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                  (coe addInt (coe (8 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (8 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (4 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt (coe (7 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_506 (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                (coe addInt (coe (2 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v3))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v3)))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                              (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                   (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt (coe (5 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (2 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v3))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                                (coe
                                                                                                   v0)
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (1 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v3)))))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
            (coe du_I'8321'_532 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                        (coe addInt (coe (9 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (6 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (9 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (7 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                (coe addInt (coe (9 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_520 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (4 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                       (coe addInt (coe (5 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                   (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                         (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                                     (coe (2 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                                              (coe (1 :: Integer)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v2)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (3 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (4 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                                           (coe v2))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                                                 (coe
                                                                                    (1 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v2)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                                             (coe
                                                                                                v2))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
                  (coe du_I'8322'_552 (coe v2)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe addInt (coe (7 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (7 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                   (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (9 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe addInt (coe (7 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                      (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_520 (coe v2)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_574))
                     (coe
                        du_cata'45'body'45'below_300 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_86
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (5 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_484 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_484 v2
du_b_484 :: Integer -> Integer
du_b_484 v0 = coe addInt (coe (10 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_486 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p0_486 v2
du_p0_486 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_486 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_488 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p1_488 v2
du_p1_488 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_488 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_490 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p2_490 v2
du_p2_490 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_490 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_492 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p3_492 v2
du_p3_492 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_492 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_494 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p4_494 v2
du_p4_494 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_494 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_496 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p5_496 v2
du_p5_496 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_496 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_498 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_498 v2
du_cl'60'b_498 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_498 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (7 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_500 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_500 v2
du_k'60'b_500 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_500 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (8 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_502 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_502 v2
du_ev'60'b_502 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_502 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (9 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_504 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_504 v2
du_pr'60'b_504 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_504 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (10 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_506 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_506 v2
du_setup_506 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_506 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b_502 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b_500 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b_504 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b_502 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_cl'60'b_498 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                         (coe du_k'60'b_500 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_520 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_520 v2
du_call_520 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_520 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b_500 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b_504 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b_500 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b_498 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_pr'60'b_504 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_532 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_532 v2
du_I'8321'_532 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_532 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_p3_492 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_p5_496 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe du_p2_490 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                (coe du_p1_488 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                      (coe du_p5_496 (coe v0)) erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                            (coe du_p3_492 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                  (coe du_p1_488 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                     (coe du_p3_492 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                        (coe du_p2_490 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_552 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_552 v2
du_I'8322'_552 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_552 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_p4_494 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_p3_492 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_p5_496 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                 (coe du_p3_492 (coe v0)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_p1_488 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_p5_496 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                   (coe du_p4_494 (coe v0)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                            (coe du_p0_486 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                        (coe du_p1_488 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                              (coe
                                                                                 du_p0_486 (coe v0))
                                                                              erased)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_574
du_I'8323'_574 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_574
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.push2-below
d_push2'45'below_584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_push2'45'below_584 v5 v6 v7
du_push2'45'below_584 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_584 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
         erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v2)
               erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
                     erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
                           erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v2)
                                 erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.pop2-below
d_pop2'45'below_616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_616 ~v0 ~v1 ~v2 v3 = du_pop2'45'below_616 v3
du_pop2'45'below_616 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_616 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
         erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
                  erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.SlotBudget.wrap-sum-below
d_wrap'45'sum'45'below_634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_634 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_wrap'45'sum'45'below_634 v4 v5
du_wrap'45'sum'45'below_634 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_634 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
         erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
               erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v0)
                           erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74 (coe v1)
                                 erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
-- Once.CCC.Codegen.SlotBudget.visit-below
d_visit'45'below_668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'below_668 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_visit'45'below_668 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_visit'45'below_668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_visit'45'below_668 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_112 v11
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
             (coe du_push2'45'below_584 (coe v7) (coe v8) (coe v9))
      MAlonzo.Code.Once.Type.C__'8853'__116 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11)))
                      (coe v6)))
                (coe
                   du_visit'45'below_668 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11)))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_742 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                         (coe v0) (coe v2) (coe v3) (coe v4) (coe v11)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         du_visit'45'below_668 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v7) (coe v8)
                         (coe v9) (coe du_recF_738 (coe v11) (coe v12) (coe v5) (coe v10)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe du_s'60'b_778 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v11)
                   (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                (coe
                   du_visit'45'below_668 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                   (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v7)
                   (coe v8) (coe v9)
                   (coe du_recF_782 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe du_s'60'b_778 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_668 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                      (coe addInt (coe (4 :: Integer)) (coe v5))
                      (coe
                         addInt
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11))
                         (coe v6))
                      (coe v7) (coe v8) (coe v9)
                      (coe du_recG_786 (coe v11) (coe v12) (coe v5) (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_738 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_738 v1 v2 v6 v12
du_recF_738 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_738 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_742 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_742 v1 v2 v6 v12
du_recG_742 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_742 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_774 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_room4_774 v1 v2 v6 v12
du_room4_774 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_774 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v2 (4 :: Integer)
         (mulInt
            (coe (4 :: Integer))
            (coe
               addInt
               (coe
                  addInt (coe (1 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_778 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_s'60'b_778 v1 v2 v6 v12
du_s'60'b_778 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_778 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_774 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_782 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_782 v1 v2 v6 v12
du_recF_782 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_782 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_786 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_786 v1 v2 v6 v12
du_recG_786 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_786 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.rebuild-below
d_rebuild'45'below_808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'below_808 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_rebuild'45'below_808 v0 v1 v2 v5 v6 v8 v9
du_rebuild'45'below_808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_808 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_112 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe du_pop2'45'below_616 (coe v5)
      MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                   (coe v0) (coe v2) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7)))
                      (coe v4)))
                (coe
                   du_rebuild'45'below_808 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7)))
                      (coe v4))
                   (coe v5) (coe du_recG_882 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                      (coe (1 :: Integer)) (coe v3))
                   (coe
                      du_wrap'45'sum'45'below_634
                      (coe du_s'60'b_870 (coe v7) (coe v8) (coe v3) (coe v6))
                      (coe du_b'45'ss_874 (coe v7) (coe v8) (coe v3) (coe v6)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                            (coe v0) (coe v2) (coe v7)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            du_rebuild'45'below_808 (coe v0) (coe v7) (coe v2)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5)
                            (coe du_recF_878 (coe v7) (coe v8) (coe v3) (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                               (coe (0 :: Integer)) (coe v3))
                            (coe
                               du_wrap'45'sum'45'below_634
                               (coe du_s'60'b_870 (coe v7) (coe v8) (coe v3) (coe v6))
                               (coe du_b'45'ss_874 (coe v7) (coe v8) (coe v3) (coe v6)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe du_s'60'b_914 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                   (coe v0) (coe v2) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7))
                      (coe v4)))
                (coe
                   du_rebuild'45'below_808 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7))
                      (coe v4))
                   (coe v5) (coe du_recG_938 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                         (coe addInt (coe (2 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe du_b'45's2_922 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe du_s'60'b_914 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                         (coe v0) (coe v2) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                      (coe
                         du_rebuild'45'below_808 (coe v0) (coe v7) (coe v2)
                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v5)
                         (coe du_recF_934 (coe v7) (coe v8) (coe v3) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe du_b'45'ss_918 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                  (coe du_b'45's3_928 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                        (coe du_b'45'ss_918 (coe v7) (coe v8) (coe v3) (coe v6))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                              (coe
                                                 du_b'45's2_922 (coe v7) (coe v8) (coe v3) (coe v6))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                    (coe
                                                       du_b'45's3_928 (coe v7) (coe v8) (coe v3)
                                                       (coe v6))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_866 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_866 v1 v2 v6 v10
du_room4_866 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_866 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v2 (4 :: Integer)
         (mulInt
            (coe (4 :: Integer))
            (coe
               addInt
               (coe
                  addInt (coe (1 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_870 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_870 v1 v2 v6 v10
du_s'60'b_870 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_870 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_866 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45'ss_874 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_874 v1 v2 v6 v10
du_b'45'ss_874 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_874 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_866 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_878 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_878 v1 v2 v6 v10
du_recF_878 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_878 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_882 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_882 v1 v2 v6 v10
du_recG_882 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_910 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_910 v1 v2 v6 v10
du_room4_910 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_910 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v2 (4 :: Integer)
         (mulInt
            (coe (4 :: Integer))
            (coe
               addInt
               (coe
                  addInt (coe (1 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_914 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_914 v1 v2 v6 v10
du_s'60'b_914 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_914 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_910 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45'ss_918 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_918 v1 v2 v6 v10
du_b'45'ss_918 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_918 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_910 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45's2_922 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's2_922 v1 v2 v6 v10
du_b'45's2_922 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_922 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_910 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45's3_928 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's3_928 v1 v2 v6 v10
du_b'45's3_928 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_928 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_910 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_934 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_934 v1 v2 v6 v10
du_recF_934 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_934 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_938 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_938 v1 v2 v6 v10
du_recG_938 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_938 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt (coe (4 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
            v2
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (addInt (coe v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (addInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.visit-idle
d_visit'45'idle_970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_970 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1032 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'branching'45'below_1092 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe
                  addInt
                  (coe
                     addInt (coe (13 :: Integer))
                     (coe
                        mulInt (coe (4 :: Integer))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                  (coe v3)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe
                        addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe
                              mulInt (coe (4 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                           (coe
                              addInt
                              (coe
                                 addInt (coe (14 :: Integer))
                                 (coe
                                    mulInt (coe (4 :: Integer))
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                       (coe v1))))
                              (coe v3)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (13 :: Integer))
                                       (coe
                                          mulInt (coe (4 :: Integer))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                             (coe v1))))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe
                                             addInt
                                             (coe
                                                addInt (coe (11 :: Integer))
                                                (coe
                                                   mulInt (coe (4 :: Integer))
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                      (coe v1))))
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt
                                                            (coe
                                                               addInt
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                                     (coe v1)))
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                                  (coe v1)))
                                                            (coe v4))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                            (coe
                                                               addInt
                                                               (coe
                                                                  addInt (coe (12 :: Integer))
                                                                  (coe
                                                                     mulInt (coe (4 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                                        (coe v1))))
                                                               (coe v3)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                  (coe
                     addInt
                     (coe
                        addInt (coe (13 :: Integer))
                        (coe
                           mulInt (coe (4 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                     (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe
                           addInt
                           (coe
                              addInt (coe (12 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                              (coe
                                 addInt
                                 (coe
                                    addInt (coe (14 :: Integer))
                                    (coe
                                       mulInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                          (coe v1))))
                                 (coe v3)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe
                                       addInt
                                       (coe
                                          addInt (coe (13 :: Integer))
                                          (coe
                                             mulInt (coe (4 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                (coe v1))))
                                       (coe v3)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                             (coe
                                                addInt
                                                (coe
                                                   addInt (coe (11 :: Integer))
                                                   (coe
                                                      mulInt (coe (4 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                         (coe v1))))
                                                (coe v3)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt
                                                               (coe
                                                                  addInt
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                                        (coe v1)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                                     (coe v1)))
                                                               (coe v4))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                               (coe
                                                                  addInt
                                                                  (coe
                                                                     addInt (coe (12 :: Integer))
                                                                     (coe
                                                                        mulInt (coe (4 :: Integer))
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                                           (coe v1))))
                                                                  (coe v3)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_1130 (coe v1) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
            (coe v0) (coe v1) (coe v3) (coe v4))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
            (coe du_b_1110 (coe v1) (coe v3))
            (coe
               du_cata'45'budget'45'of_86
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                  (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28
                     (coe v1))
                  (coe v2) (coe v3) (coe v4) (coe v5)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
               (coe v0) (coe v1) (coe v3) (coe v4))
            (coe du_b'8804'b2_1112 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
                  (coe v0) (coe v1) (coe v3) (coe v4))
               (coe du_I'8321''45'all_1190 (coe v0) (coe v1) (coe v3) (coe v4))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe
                        addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe
                              mulInt (coe (4 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                        (coe
                           addInt
                           (coe
                              addInt (coe (14 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe
                                 addInt
                                 (coe
                                    addInt (coe (12 :: Integer))
                                    (coe
                                       mulInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                          (coe v1))))
                                 (coe v3)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe
                                       addInt
                                       (coe
                                          addInt (coe (11 :: Integer))
                                          (coe
                                             mulInt (coe (4 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                (coe v1))))
                                       (coe v3)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe
                                                addInt
                                                (coe
                                                   addInt (coe (14 :: Integer))
                                                   (coe
                                                      mulInt (coe (4 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                         (coe v1))))
                                                (coe v3)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe
                           addInt
                           (coe
                              addInt (coe (12 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                           (coe
                              addInt
                              (coe
                                 addInt (coe (14 :: Integer))
                                 (coe
                                    mulInt (coe (4 :: Integer))
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                       (coe v1))))
                              (coe v3)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (12 :: Integer))
                                       (coe
                                          mulInt (coe (4 :: Integer))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                             (coe v1))))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe
                                          addInt
                                          (coe
                                             addInt (coe (11 :: Integer))
                                             (coe
                                                mulInt (coe (4 :: Integer))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                   (coe v1))))
                                          (coe v3)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                (coe
                                                   addInt
                                                   (coe
                                                      addInt (coe (14 :: Integer))
                                                      (coe
                                                         mulInt (coe (4 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
                                                            (coe v1))))
                                                   (coe v3)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_1144 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                  (coe v0) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                  (coe du_b_1110 (coe v1) (coe v3))
                  (coe
                     du_cata'45'budget'45'of_86
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28
                           (coe v1))
                        (coe v2) (coe v3) (coe v4) (coe v5)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                     (coe v0) (coe v3) (coe v4))
                  (coe du_b'8804'b2_1112 (coe v1) (coe v3))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                        (coe v0) (coe v3) (coe v4))
                     (coe du_I'8322''45'all_1224 (coe v1) (coe v3))))
               (coe
                  du_cata'45'body'45'below_300 (coe v0)
                  (coe
                     du_cata'45'budget'45'of_86
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28
                           (coe v1))
                        (coe v2) (coe v3) (coe v4) (coe v5)))
                  (coe
                     addInt
                     (coe
                        addInt
                        (coe
                           addInt (coe (5 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v1)))
                     (coe v4))
                  (coe v5) (coe v6)))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_1110 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_b_1110 v1 v3
du_b_1110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_b_1110 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.SlotBudget._.b≤b2
d_b'8804'b2_1112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'8804'b2_1112 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_b'8804'b2_1112 v1 v3
du_b'8804'b2_1112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'8804'b2_1112 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe du_b_1110 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_1116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_1116 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_bnd_1116 v1 v3 v7 v8
du_bnd_1116 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_1116 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe addInt (coe (1 :: Integer)) (coe du_b_1110 (coe v0) (coe v1)))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (coe du_b_1110 (coe v0) (coe v1))
         (addInt (coe (1 :: Integer)) (coe v2)) (4 :: Integer) v3)
-- Once.CCC.Codegen.SlotBudget._.cl<b2
d_cl'60'b2_1122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b2_1122 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_cl'60'b2_1122 v1 v3
du_cl'60'b2_1122 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b2_1122 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_b_1110 (coe v0) (coe v1))))
      (coe
         du_bnd_1116 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b2
d_k'60'b2_1124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b2_1124 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_k'60'b2_1124 v1 v3
du_k'60'b2_1124 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b2_1124 v0 v1
  = coe
      du_bnd_1116 (coe v0) (coe v1) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b2
d_ev'60'b2_1126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b2_1126 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_ev'60'b2_1126 v1 v3
du_ev'60'b2_1126 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b2_1126 v0 v1
  = coe
      du_bnd_1116 (coe v0) (coe v1) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b2
d_pr'60'b2_1128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b2_1128 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_pr'60'b2_1128 v1 v3
du_pr'60'b2_1128 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b2_1128 v0 v1
  = coe
      du_bnd_1116 (coe v0) (coe v1) (coe (3 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe
                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                  (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1130 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_setup_1130 v1 v3
du_setup_1130 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1130 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b2_1126 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b2_1124 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b2_1128 (coe v0) (coe v1)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b2_1126 (coe v0) (coe v1)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_cl'60'b2_1122 (coe v0) (coe v1)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                         (coe du_k'60'b2_1124 (coe v0) (coe v1))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1144 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_call_1144 v1 v3
du_call_1144 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1144 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b2_1124 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b2_1128 (coe v0) (coe v1)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b2_1124 (coe v0) (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b2_1122 (coe v0) (coe v1)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_pr'60'b2_1128 (coe v0) (coe v1)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1156 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7_1156 v1 v3
du_fixed7_1156 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1156 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            addInt
            (coe
               addInt (coe (7 :: Integer))
               (coe
                  mulInt (coe (4 :: Integer))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
            (coe v1)))
-- Once.CCC.Codegen.SlotBudget._.fixed7'
d_fixed7''_1158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1158 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7''_1158 v1 v3
du_fixed7''_1158 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1158 v0 v1 = coe du_fixed7_1156 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1162 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q0_1162 v1 v3
du_q0_1162 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1162 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1164 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q1_1164 v1 v3
du_q1_1164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1164 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1166 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q2_1166 v1 v3
du_q2_1166 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1166 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1170 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q3_1170 v1 v3
du_q3_1170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1170 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1174 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q4_1174 v1 v3
du_q4_1174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1174 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1178 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q5_1178 v1 v3
du_q5_1178 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1178 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1182 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q6_1182 v1 v3
du_q6_1182 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1182 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1158 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1186 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_walk'45'room_1186 v1 v3
du_walk'45'room_1186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1186 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe
         addInt
         (coe
            addInt (coe (7 :: Integer))
            (coe
               mulInt (coe (4 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
         (coe v1))
-- Once.CCC.Codegen.SlotBudget._.I₁-idle
d_I'8321''45'idle_1188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1188 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1190 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_I'8321''45'all_1190 v0 v1 v3 v4
du_I'8321''45'all_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_q3_1170 (coe v1) (coe v2)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_q6_1182 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                 (coe du_q6_1182 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_q1_1164 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_q6_1182 (coe v1) (coe v2)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe du_q2_1166 (coe v1) (coe v2)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_q6_1182 (coe v1) (coe v2)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                (coe du_q0_1162 (coe v1) (coe v2)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                   (coe du_q3_1170 (coe v1) (coe v2)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            du_push2'45'below_584 (coe du_q0_1162 (coe v1) (coe v2))
            (coe du_q4_1174 (coe v1) (coe v2))
            (coe du_q5_1178 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_q0_1162 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                 (coe du_q0_1162 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe du_q3_1170 (coe v1) (coe v2)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_q3_1170 (coe v1) (coe v2)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  du_push2'45'below_584 (coe du_q1_1164 (coe v1) (coe v2))
                  (coe du_q4_1174 (coe v1) (coe v2))
                  (coe du_q5_1178 (coe v1) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_q3_1170 (coe v1) (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                        (coe v0) (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        du_visit'45'below_668 (coe v0) (coe v1) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3))
                        (coe du_q0_1162 (coe v1) (coe v2))
                        (coe du_q4_1174 (coe v1) (coe v2))
                        (coe du_q5_1178 (coe v1) (coe v2))
                        (coe du_walk'45'room_1186 (coe v1) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_q1_1164 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                (coe du_q1_1164 (coe v1) (coe v2)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                                 (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                          (coe v1)))
                                    (coe v3)))
                              (coe
                                 du_rebuild'45'below_808 (coe v0) (coe v1)
                                 (coe addInt (coe (2 :: Integer)) (coe v2))
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                          (coe v1)))
                                    (coe v3))
                                 (coe du_q2_1166 (coe v1) (coe v2))
                                 (coe du_walk'45'room_1186 (coe v1) (coe v2)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1224 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_I'8322''45'all_1224 v1 v3
du_I'8322''45'all_1224 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1224 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_584 (coe du_q2_1166 (coe v0) (coe v1))
         (coe du_q4_1174 (coe v0) (coe v1))
         (coe du_q5_1178 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_q2_1166 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'slots'45'below_1238 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             d_cata'45'const'45'below_320 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             d_cata'45'nat'45'below_382 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             d_cata'45'linear'45'below_468 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             d_cata'45'branching'45'below_1092 (coe v0) (coe v7) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.resuspend-mono
d_resuspend'45'mono_1292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_resuspend'45'mono_1292 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          d_resuspend'45'mono_1292 (coe v0)
                          (coe addInt (coe (3 :: Integer)) (coe v1))
                          (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v10)
                          (coe v8))
                       (coe
                          d_resuspend'45'mono_1292 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v10)
                                (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                   (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v10)
                                   (coe v8))))
                          (coe v3) (coe v11) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          d_resuspend'45'mono_1292 (coe v0)
                          (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                          (coe v10) (coe v8))
                       (coe
                          d_resuspend'45'mono_1292 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                (coe v3) (coe v10) (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                   (coe v3) (coe v10) (coe v8))))
                          (coe v3) (coe v11) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.resuspend-below
d_resuspend'45'below_1336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_resuspend'45'below_1336 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v7
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v7))))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                      (coe v0) (coe v1) (coe v2) (coe v3)
                      (coe MAlonzo.Code.Once.IRTy.C_Id_10) (coe v5))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe addInt (coe (1 :: Integer)) (coe v1)))
                   erased)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                         erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                               erased)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                              (coe addInt (coe (2 :: Integer)) (coe v1)))
                                           erased)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                          (coe v1))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                                   (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                          (coe
                             d_n'60'B_1432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                             (coe v11) (coe v8) (coe v9))
                          erased)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                d_n'60'B_1432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                (coe v11) (coe v8) (coe v9))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                         (coe v0)
                                         (coe
                                            du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                            (coe v8))
                                         (coe
                                            du_l2_1422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                            (coe v8))
                                         (coe v3) (coe v11) (coe v9))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                         (coe (2 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                            (coe addInt (coe (1 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                  (coe addInt (coe (2 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                        (coe (1 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v1)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                       (coe
                          d_arm_1438 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11)
                          (coe v8) (coe v9) (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0)
                                   (coe
                                      du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v8))
                                   (coe
                                      du_l2_1422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v8))
                                   (coe v3) (coe v11) (coe v9))))
                          (coe
                             d_resuspend'45'below_1336 (coe v0)
                             (coe
                                du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v8))
                             (coe
                                du_l2_1422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v8))
                             (coe v3) (coe v11) (coe v9)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v2)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                                   (coe v1))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                               (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                               (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                               (coe v10) (coe v8))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                               (coe (2 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                        (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                                              (coe (0 :: Integer)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                             (coe
                                d_arm_1438 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11)
                                (coe v8) (coe v9) (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                         (coe v10) (coe v8))))
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                                   (coe
                                      du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v8))
                                   (coe
                                      d_B_1424 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v11) (coe v8) (coe v9))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                            (coe v10) (coe v8))))
                                   (coe
                                      d_mid_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v11) (coe v8) (coe v9))
                                   (coe
                                      d_resuspend'45'below_1336 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1))
                                      (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v10)
                                      (coe v8))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                          (coe v1))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                          (coe
                             d_n'60'B_1384 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                             (coe v11) (coe v8) (coe v9))
                          erased)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                d_n'60'B_1384 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                (coe v11) (coe v8) (coe v9))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                (coe v3) (coe v10) (coe v8))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                          (coe
                             du_n2_1372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v8))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v8 v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                   (coe v3) (coe v10) (coe v8))))
                          (coe
                             d_mid_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11)
                             (coe v8) (coe v9))
                          (coe
                             d_resuspend'45'below_1336 (coe v0)
                             (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                             (coe v10) (coe v8)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                (coe addInt (coe (2 :: Integer)) (coe v1)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                   (coe (2 :: Integer)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                      (coe addInt (coe (1 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                (coe
                                   d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                   (coe v11) (coe v8) (coe v9))
                                erased)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                      (coe
                                         d_sn'60'B_1382 (coe v0) (coe v1) (coe v2) (coe v3)
                                         (coe v10) (coe v11) (coe v8) (coe v9))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                            (coe
                                               d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3)
                                               (coe v10) (coe v11) (coe v8) (coe v9))
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                  (coe
                                                     d_n'60'B_1384 (coe v0) (coe v1) (coe v2)
                                                     (coe v3) (coe v10) (coe v11) (coe v8) (coe v9))
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                      (coe v0)
                                      (coe
                                         du_n2_1372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                         (coe v8))
                                      (coe
                                         du_l2_1374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                         (coe v8))
                                      (coe v3) (coe v11) (coe v9))))
                             (coe
                                d_resuspend'45'below_1336 (coe v0)
                                (coe
                                   du_n2_1372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                   (coe v8))
                                (coe
                                   du_l2_1374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                   (coe v8))
                                (coe v3) (coe v11) (coe v9))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                                         (coe addInt (coe (1 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                      (coe
                                         d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                         (coe v11) (coe v8) (coe v9))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                         (coe
                                            d_sn'60'B_1382 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v10) (coe v11) (coe v8) (coe v9))
                                         erased)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                            (coe
                                               d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3)
                                               (coe v10) (coe v11) (coe v8) (coe v9))
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                  (coe
                                                     d_sn'60'B_1382 (coe v0) (coe v1) (coe v2)
                                                     (coe v3) (coe v10) (coe v11) (coe v8) (coe v9))
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.n2
d_n2_1372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_n2_1372 v0 v1 v2 v3 v4 ~v5 v6 ~v7 = du_n2_1372 v0 v1 v2 v3 v4 v6
du_n2_1372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_1372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
         (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.l2
d_l2_1374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_l2_1374 v0 v1 v2 v3 v4 ~v5 v6 ~v7 = du_l2_1374 v0 v1 v2 v3 v4 v6
du_l2_1374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_1374 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
            (coe v3) (coe v4) (coe v5)))
-- Once.CCC.Codegen.SlotBudget._.B
d_B_1376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_B_1376 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0)
         (coe
            du_n2_1372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe
            du_l2_1374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe v3) (coe v5) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.mid
d_mid_1378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mid_1378 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_resuspend'45'mono_1292 (coe v0)
      (coe
         du_n2_1372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe
         du_l2_1374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe v3) (coe v5) (coe v7)
-- Once.CCC.Codegen.SlotBudget._.base
d_base_1380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base_1380 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_resuspend'45'mono_1292 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
         (coe v4) (coe v6))
      (coe
         d_mid_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.sn<B
d_sn'60'B_1382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'B_1382 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe
         d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.n<B
d_n'60'B_1384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'B_1384 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         d_base_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.n2
d_n2_1420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_n2_1420 v0 v1 v2 v3 v4 ~v5 v6 ~v7 = du_n2_1420 v0 v1 v2 v3 v4 v6
du_n2_1420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_1420 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v5))
-- Once.CCC.Codegen.SlotBudget._.l2
d_l2_1422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_l2_1422 v0 v1 v2 v3 v4 ~v5 v6 ~v7 = du_l2_1422 v0 v1 v2 v3 v4 v6
du_l2_1422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_1422 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
            (coe v5)))
-- Once.CCC.Codegen.SlotBudget._.B
d_B_1424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_B_1424 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0)
         (coe
            du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe
            du_l2_1422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe v3) (coe v5) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.mid
d_mid_1426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mid_1426 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_resuspend'45'mono_1292 (coe v0)
      (coe
         du_n2_1420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe
         du_l2_1422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe v3) (coe v5) (coe v7)
-- Once.CCC.Codegen.SlotBudget._.base
d_base_1428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base_1428 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_resuspend'45'mono_1292 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v6))
      (coe
         d_mid_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.sn<B
d_sn'60'B_1430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'B_1430 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe
         d_base_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.n<B
d_n'60'B_1432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'B_1432 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         d_base_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.SlotBudget._.arm
d_arm_1438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_arm_1438 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
            (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe
               d_n'60'B_1432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7))
            erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe v9) (coe v10)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                        (coe addInt (coe (1 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                              (coe addInt (coe (2 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296
                                    (coe v8))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe
                     d_base_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                     (coe v6) (coe v7))
                  erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe
                           d_sn'60'B_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v6) (coe v7))
                        erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe
                                 d_base_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                 (coe v6) (coe v7))
                              erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe
                                             d_sn'60'B_1430 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_1468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_slots'45'below_1468 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v1) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_id_20)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_budget'45'of_78
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10)))
                (coe
                   du_trace'45'of_82
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   d_frontier'45'mono_150 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
                (coe
                   d_slots'45'below_1468 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                   (coe v5)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_1468 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                             (coe v4))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                   (coe addInt (coe (1 :: Integer)) (coe v4)))
                                (coe
                                   d_h_1510 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9) (coe v10)
                                   (coe v4) (coe v5)))
                             erased)
                          (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          du_trace'45'of_82
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             du_budget'45'of_78
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10)))
                          (coe
                             du_trace'45'of_82
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             d_frontier'45'mono_150 (coe v0) (coe v1) (coe v12) (coe v10)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                      (coe v9)))))
                          (coe
                             d_slots'45'below_1468 (coe v0) (coe v1) (coe v11) (coe v9)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
                                   (coe v4))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   (coe
                                      d_h_1510 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                      (coe v10) (coe v4) (coe v5)))
                                erased)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                      (coe
                                         d_h_1510 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                         (coe v10) (coe v4) (coe v5)))
                                   erased)
                                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                             (coe
                                du_trace'45'of_82
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v1) (coe v12)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                            (coe v0) (coe v1) (coe v11)
                                            (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                            (coe v9))))
                                   (coe v10)))
                             (coe
                                d_slots'45'below_1468 (coe v0) (coe v1) (coe v12) (coe v10)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300
                                         (coe (2 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
                                            (coe addInt (coe (3 :: Integer)) (coe v4)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                                                              (coe
                                                                 addInt (coe (3 :: Integer))
                                                                 (coe v4)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                            (coe addInt (coe (3 :: Integer)) (coe v4)))
                                         (coe
                                            d_h_1510 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                            (coe v10) (coe v4) (coe v5)))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                            (coe
                                               d_h_1510 (coe v0) (coe v1) (coe v11) (coe v12)
                                               (coe v9) (coe v10) (coe v4) (coe v5))
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     (coe
                                                        d_h_1510 (coe v0) (coe v1) (coe v11)
                                                        (coe v12) (coe v9) (coe v10) (coe v4)
                                                        (coe v5)))
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 addInt (coe (3 :: Integer))
                                                                 (coe v4)))
                                                           (coe
                                                              d_h_1510 (coe v0) (coe v1) (coe v11)
                                                              (coe v12) (coe v9) (coe v10) (coe v4)
                                                              (coe v5)))
                                                        erased)
                                                     (coe
                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                        (coe
                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                              (coe
                                                                 d_h_1510 (coe v0) (coe v1)
                                                                 (coe v11) (coe v12) (coe v9)
                                                                 (coe v10) (coe v4) (coe v5))
                                                              erased)
                                                           (coe
                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v9))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_fst_42)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_48
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_snd_48)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v9)) (coe v4)
                          (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_54)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   erased)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))
                                               erased)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_60
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v8) (coe v1)) (coe v4)
                          (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_60)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   erased)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))
                                               erased)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          du_trace'45'of_82
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v12) (coe v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                             (coe v10)))
                       (coe
                          d_slots'45'below_1468 (coe v0) (coe v12) (coe v2) (coe v10)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                             (coe
                                du_trace'45'of_82
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   du_budget'45'of_78
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                      (coe MAlonzo.Code.Once.IR.C_case_68 v9 v10)))
                                (coe
                                   du_trace'45'of_82
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   d_frontier'45'mono_150 (coe v0) (coe v12) (coe v2) (coe v10)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                         (coe v0) (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                            (coe v0) (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                                (coe
                                   d_slots'45'below_1468 (coe v0) (coe v11) (coe v2) (coe v9)
                                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_terminal_72)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v2) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_initial_76)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_curry_84 v9)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                      erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                               (coe addInt (coe (2 :: Integer)) (coe v4)))
                            erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                     (coe addInt (coe (1 :: Integer)) (coe v4)))
                                  erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe addInt (coe (2 :: Integer)) (coe v4)))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
      MAlonzo.Code.Once.IR.C_apply_90
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                      -> coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                           (coe
                              du_trace'45'of_82
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v10) (coe v2))
                                    (coe v10))
                                 (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_apply_90)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v4)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v4)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v4)))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v4)))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_In_94 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           d_cata'45'slots'45'below_1238 (coe v0)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v13)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                       (coe v2)))
                                 (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                          (coe v2)))
                                    (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10)))))
                           (coe
                              d_slots'45'below_1468 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                    (coe v2)))
                              (coe v2) (coe v10) (coe (0 :: Integer)) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_Out_110 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_114 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   erased)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                            (coe addInt (coe (1 :: Integer)) (coe v4)))
                                         erased)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_120 v7 v9
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_120 v7 v9)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                      erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                               (coe addInt (coe (2 :: Integer)) (coe v4)))
                            erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                     (coe addInt (coe (1 :: Integer)) (coe v4)))
                                  erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe addInt (coe (2 :: Integer)) (coe v4)))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
      MAlonzo.Code.Once.IR.C_const_124 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_520
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_124 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_522
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_82
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_124 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_130 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7)) (coe v4)
                   (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_Call_136 v8
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_82
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Call_136 v8)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1510 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_150 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_150 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_78
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget.bodies-of
d_bodies'45'of_1652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bodies'45'of_1652 ~v0 v1 = du_bodies'45'of_1652 v1
du_bodies'45'of_1652 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bodies'45'of_1652 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.blocks-below
d_blocks'45'below_1666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'below_1666 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_bodies'45'of_1652
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                d_blocks'45'below_1666 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_blocks'45'below_1666 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bodies'45'of_1652
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v1) (coe v11)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                    (coe
                       d_blocks'45'below_1666 (coe v0) (coe v1) (coe v11) (coe v9)
                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       d_blocks'45'below_1666 (coe v0) (coe v1) (coe v12) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bodies'45'of_1652
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                          (coe v0) (coe v11) (coe v2) (coe v4)
                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                    (coe
                       d_blocks'45'below_1666 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_blocks'45'below_1666 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (d_slots'45'below_1468
                       (coe v0)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                       (coe v11) (coe v9) (coe (0 :: Integer))
                       (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (d_blocks'45'below_1666
                       (coe v0)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                       (coe v11) (coe v9) (coe (0 :: Integer))
                       (coe addInt (coe (2 :: Integer)) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           d_blocks'45'below_1666 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13) (coe v2)))
                           (coe v2) (coe v10) (coe (0 :: Integer)) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Ana_120 v7 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          du_trace'45'of_82
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                             (coe v0) (coe v1)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                             (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                             (coe v9)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                                (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                         (coe v1))
                                      (coe (0 :: Integer))
                                      (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                         (coe v0) (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                            (coe v1))
                                         (coe (0 :: Integer))
                                         (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v9))))
                                (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))
                                (coe v10) (coe v7)))
                          (coe
                             du_trace'45'of_82
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                                (coe v9)))
                          (coe
                             d_resuspend'45'mono_1292 (coe v0)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                      (coe v1))
                                   (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                      (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                         (coe v1))
                                      (coe (0 :: Integer))
                                      (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v9))))
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))
                             (coe v10) (coe v7))
                          (coe
                             d_slots'45'below_1468 (coe v0) (coe v1)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                             (coe v9) (coe (0 :: Integer))
                             (coe addInt (coe (1 :: Integer)) (coe v5))))
                       (coe
                          d_resuspend'45'below_1336 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                (coe v0) (coe v1)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                                (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                                   (coe v0) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                      (coe v1))
                                   (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
                                   (coe v9))))
                          (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))
                          (coe v10) (coe v7)))
                    (d_blocks'45'below_1666
                       (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                       (coe v9) (coe (0 :: Integer))
                       (coe addInt (coe (1 :: Integer)) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v7 v8
        -> coe
             seq (coe v7)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_SigOp_130 v6 v7 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Call_136 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-all
d_ir'45'slots'45'below'45'all_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'all_1784 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_82
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1468
            (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
            (MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'blocks_720
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_824
                  (coe v0) (coe v1) (coe v2) (coe v3))
               (coe
                  du_bodies'45'of_1652
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                     (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                     (coe (0 :: Integer)) (coe v3)))
               (coe
                  d_blocks'45'below_1666 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe (0 :: Integer)) (coe (0 :: Integer))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.SlotBudget.emitted-slot-seg
d_emitted'45'slot'45'seg_1802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_1802 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_emitted'45'slot'45'seg_1802 v0 v1 v2 v3 v4 v6
du_emitted'45'slot'45'seg_1802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_1802 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_below_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45'at_980
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4)
         (coe
            d_ir'45'slots'45'below'45'all_1784 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      v5 erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-under-lab
d_ir'45'slots'45'below'45'under'45'lab_1826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'under'45'lab_1826 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_82
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer)) (coe v4) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1468
            (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer)) (coe v4))
         v5)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
            (MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'blocks_720
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_cur_150
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_pop'45'with_170 (coe v5)
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_mkSeg_154
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
                           (coe v0) (coe v1) (coe v2) (coe v4) (coe v3))
                        (coe v5))))
               (coe
                  du_bodies'45'of_1652
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                     (coe v0) (coe v1) (coe v2) (coe (0 :: Integer)) (coe v4) (coe v3)))
               (coe
                  d_blocks'45'below_1666 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe (0 :: Integer)) (coe v4)))
            (MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_saved_152
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_pop'45'with_170 (coe v5)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_mkSeg_154
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
                        (coe v0) (coe v1) (coe v2) (coe v4) (coe v3))
                     (coe v5))))))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold-lab
d_ir'45'seg'45'fold'45'lab_1846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold'45'lab_1846 = erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-top
d_ir'45'slots'45'below'45'top_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'top_1864 v0 v1 v2 v3 ~v4 v5
  = du_ir'45'slots'45'below'45'top_1864 v0 v1 v2 v3 v5
du_ir'45'slots'45'below'45'top_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
du_ir'45'slots'45'below'45'top_1864 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_82
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1468
            (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer))
            (coe (0 :: Integer)))
         v4)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
               (MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'blocks_720
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_824
                     (coe v0) (coe v1) (coe v2) (coe v3))
                  (coe
                     du_bodies'45'of_1652
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
                        (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                        (coe (0 :: Integer)) (coe v3)))
                  (coe
                     d_blocks'45'below_1666 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe (0 :: Integer)) (coe (0 :: Integer))))
               v4)))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold-top
d_ir'45'seg'45'fold'45'top_1884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold'45'top_1884 = erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-under
d_ir'45'slots'45'below'45'under_1900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'under_1900 v0 v1 v2 v3
  = coe
      d_ir'45'slots'45'below'45'under'45'lab_1826 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe (0 :: Integer))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold
d_ir'45'seg'45'fold_1912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold_1912 = erased
