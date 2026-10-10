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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotSeg
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.SlotBudget._.CataStrategy
d_CataStrategy_12 a0 = ()
-- Once.CCC.Codegen.SlotBudget._.cata-body
d_cata'45'body_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'br'45'I'8321'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₂
d_cata'45'br'45'I'8322'_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'br'45'I'8322'_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-dispatch
d_cata'45'dispatch_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.fsize
d_fsize_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
d_fsize_24 ~v0 = du_fsize_24
du_fsize_24 :: MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
du_fsize_24
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget
d_ir'45'stack'45'budget_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_26 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_28 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace
d_ir'45'to'45'trace_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace_30 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_860
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace'
d_ir'45'to'45'trace''_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_32 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace'45'lab_34 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_936
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-unit
d_ir'45'to'45'unit_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2326
d_ir'45'to'45'unit_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_854
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.pop2
d_pop2_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_pop2_40 ~v0 = du_pop2_40
du_pop2_40 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_pop2_40
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_182
-- Once.CCC.Codegen.SlotBudget._.push2
d_push2_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_push2_42 ~v0 = du_push2_42
du_push2_42 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_push2_42
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
-- Once.CCC.Codegen.SlotBudget._.rebuild-walk
d_rebuild'45'walk_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_rebuild'45'walk_44 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.SlotBudget._.resuspend-layer
d_resuspend'45'layer_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.sigop-budget
d_sigop'45'budget_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
d_sigop'45'budget_48 ~v0 = du_sigop'45'budget_48
du_sigop'45'budget_48 ::
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
du_sigop'45'budget_48
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'budget_502
-- Once.CCC.Codegen.SlotBudget._.sigop-code
d_sigop'45'code_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_sigop'45'code_50 ~v0 = du_sigop'45'code_50
du_sigop'45'code_50 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_sigop'45'code_50
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'code_512
-- Once.CCC.Codegen.SlotBudget._.visit-walk
d_visit'45'walk_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_visit'45'walk_60 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.wrap-sum
d_wrap'45'sum_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_wrap'45'sum_62 ~v0 = du_wrap'45'sum_62
du_wrap'45'sum_62 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_wrap'45'sum_62
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_74 ~v0 v1 = du_budget'45'of_74 v1
du_budget'45'of_74 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_74 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace'45'of_78 ~v0 v1 = du_trace'45'of_78 v1
du_trace'45'of_78 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_trace'45'of_78 v0
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
d_cata'45'budget'45'of_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_82 ~v0 v1 = du_cata'45'budget'45'of_82 v1
du_cata'45'budget'45'of_82 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'budget'45'of_82 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'trace'45'of_86 ~v0 v1 = du_cata'45'trace'45'of_86 v1
du_cata'45'trace'45'of_86 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_cata'45'trace'45'of_86 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_100 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_cata'45'mono_100 v1 v3
du_cata'45'mono_100 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_100 v0 v1
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
-- Once.CCC.Codegen.SlotBudget.sigop-mono
d_sigop'45'mono_140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sigop'45'mono_140 ~v0 v1 v2 = du_sigop'45'mono_140 v1 v2
du_sigop'45'mono_140 ::
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sigop'45'mono_140 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v0))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v0)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.frontier-mono
d_frontier'45'mono_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_156 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_156 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_frontier'45'mono_156 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   du_budget'45'of_74
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                          d_frontier'45'mono_156 (coe v0) (coe v1) (coe v11) (coe v9)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                       (coe
                          d_frontier'45'mono_156 (coe v0) (coe v1) (coe v12) (coe v10)
                          (coe
                             du_budget'45'of_74
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       d_frontier'45'mono_156 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_frontier'45'mono_156 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          du_budget'45'of_74
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                           du_cata'45'mono_100
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
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v4)))
      MAlonzo.Code.Once.IR.C_const_126 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_SigOp_132 v6 v7 v8
        -> coe
             du_sigop'45'mono_140 (coe v4)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v8)))
      MAlonzo.Code.Once.IR.C_Call_138 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.lt-refl
d_lt'45'refl_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_270 ~v0 v1 = du_lt'45'refl_270 v1
du_lt'45'refl_270 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lt'45'refl_270 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_278 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'nat'45'layer'45'below_278 v4 v5
du_cata'45'nat'45'layer'45'below_278 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_278 v0 v1
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
d_cata'45'body'45'below_308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'body'45'below_308 v0 v1 ~v2 v3 ~v4 v5 v6
  = du_cata'45'body'45'below_308 v0 v1 v3 v5 v6
du_cata'45'body'45'below_308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
du_cata'45'body'45'below_308 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
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
d_cata'45'const'45'below_328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'const'45'below_328 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (2 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (1 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (2 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0) (coe v3)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe addInt (coe (2 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (1 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                             (coe v2))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0) (coe v3)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_ev'60'b_356 (coe v2)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_k'60'b_354 (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_pr'60'b_358 (coe v2)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_ev'60'b_356 (coe v2)) erased)
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
                                             (coe du_cl'60'b_352 (coe v2)) erased)
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
                                                               (coe du_k'60'b_354 (coe v2)) erased)
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
                                                                        (coe du_k'60'b_354 (coe v2))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                           (coe
                                                                              du_pr'60'b_358
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
                                                                                    du_k'60'b_354
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
                                                                                          du_cl'60'b_352
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
                                                                                                   du_pr'60'b_358
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
         du_cata'45'body'45'below_308 (coe v0)
         (coe
            du_cata'45'budget'45'of_82
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
               (coe v0)
               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22)
               (coe v1) (coe v2) (coe v3) (coe v4)))
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_346 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 = du_bnd_346 v2 v6 v7
du_bnd_346 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_346 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v0 (addInt (coe (1 :: Integer)) (coe v1)) (4 :: Integer) v2)
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_352 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_352 v2
du_cl'60'b_352 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_352 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
      (coe
         du_bnd_346 (coe v0) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_354 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_354 v2
du_k'60'b_354 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_354 v0
  = coe
      du_bnd_346 (coe v0) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_356 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_356 v2
du_ev'60'b_356 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_356 v0
  = coe
      du_bnd_346 (coe v0) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_358 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_358 v2
du_pr'60'b_358 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_358 v0
  = coe
      du_bnd_346 (coe v0) (coe (3 :: Integer))
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
d_cata'45'nat'45'below_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'nat'45'below_390 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (4 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (4 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (6 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe addInt (coe (4 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (4 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (6 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_420 (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                      (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0) (coe v3))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v3)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                            (coe (0 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                                 (coe
                                                                                    (0 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                   (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (3 :: Integer)) (coe v3)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                               (coe v0)
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v3)))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                               (coe (0 :: Integer)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                                           (coe (2 :: Integer)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
            (coe du_I'8321'_446 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                        (coe addInt (coe (5 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (2 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                (coe addInt (coe (5 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_434 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                           (coe addInt (coe (4 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (5 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                             (coe (1 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (4 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (5 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                    (coe v2))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                (coe (1 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
                  (coe du_I'8322'_456 (coe v2)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (3 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                   (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (5 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                      (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_434 (coe v2)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (5 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (4 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                          (coe addInt (coe (5 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_466))
                     (coe
                        du_cata'45'body'45'below_308 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_82
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (7 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_406 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_406 v2
du_b_406 :: Integer -> Integer
du_b_406 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_408 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p'60'b_408 v2
du_p'60'b_408 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_408 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_410 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_s'60'b_410 v2
du_s'60'b_410 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_410 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_412 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_412 v2
du_cl'60'b_412 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_412 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_414 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_414 v2
du_k'60'b_414 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_414 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_416 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_416 v2
du_ev'60'b_416 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_416 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_418 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_418 v2
du_pr'60'b_418 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_418 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_420 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_420 v2
du_setup_420 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_420 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b_416 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b_414 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b_418 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b_416 (coe v0)) erased)
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
                                       (coe du_cl'60'b_412 (coe v0)) erased)
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
                                                         (coe du_k'60'b_414 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_434 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_434 v2
du_call_434 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_434 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b_414 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b_418 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b_414 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b_412 (coe v0)) erased)
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
                                    (coe du_pr'60'b_418 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_446 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_446 v2
du_I'8321'_446 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_446 v0
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
                                                               (coe du_p'60'b_408 (coe v0)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                     (coe du_s'60'b_410 (coe v0))
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
                                                                                    du_p'60'b_408
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
                                                                                          du_s'60'b_410
                                                                                          (coe v0))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_456 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_456 v2
du_I'8322'_456 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_456 v0
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
                     (coe du_p'60'b_408 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_s'60'b_410 (coe v0)) erased)
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
                                       (coe du_p'60'b_408 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_s'60'b_410 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_466
du_I'8323'_466 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_466
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
d_cata'45'linear'45'below_476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'linear'45'below_476 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (8 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (8 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (4 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (7 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe addInt (coe (8 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (8 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (4 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                               (coe
                                                                  addInt (coe (7 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_514 (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (2 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v3))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                              (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                   (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                               (coe
                                                                  addInt (coe (5 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (2 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v3))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
            (coe du_I'8321'_540 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                        (coe addInt (coe (9 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (6 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (9 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (7 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                (coe addInt (coe (9 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_528 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (4 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                       (coe addInt (coe (5 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                   (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                         (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                                     (coe (2 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                              (coe (1 :: Integer)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v2)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (3 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (4 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                           (coe v2))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                                 (coe
                                                                                    (1 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v2)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                             (coe
                                                                                                v2))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
                  (coe du_I'8322'_560 (coe v2)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (7 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (7 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                   (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (9 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (7 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                      (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_528 (coe v2)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_582))
                     (coe
                        du_cata'45'body'45'below_308 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_82
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (5 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_492 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_492 v2
du_b_492 :: Integer -> Integer
du_b_492 v0 = coe addInt (coe (10 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_494 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p0_494 v2
du_p0_494 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_494 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_496 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p1_496 v2
du_p1_496 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_496 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_498 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p2_498 v2
du_p2_498 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_498 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_500 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p3_500 v2
du_p3_500 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_500 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_502 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p4_502 v2
du_p4_502 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_502 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_504 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p5_504 v2
du_p5_504 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_504 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_506 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_506 v2
du_cl'60'b_506 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_506 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (7 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_508 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_508 v2
du_k'60'b_508 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_508 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (8 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_510 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_510 v2
du_ev'60'b_510 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_510 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (9 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_512 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_512 v2
du_pr'60'b_512 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_512 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (10 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_514 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_514 v2
du_setup_514 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_514 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b_510 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b_508 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b_512 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b_510 (coe v0)) erased)
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
                                       (coe du_cl'60'b_506 (coe v0)) erased)
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
                                                         (coe du_k'60'b_508 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_528 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_528 v2
du_call_528 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_528 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b_508 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b_512 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b_508 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b_506 (coe v0)) erased)
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
                                    (coe du_pr'60'b_512 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_540 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_540 v2
du_I'8321'_540 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_540 v0
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
               (coe du_p3_500 (coe v0)) erased)
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
                                    (coe du_p5_504 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe du_p2_498 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                (coe du_p1_496 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                      (coe du_p5_504 (coe v0)) erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                            (coe du_p3_500 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                  (coe du_p1_496 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                     (coe du_p3_500 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                                        (coe du_p2_498 (coe v0))
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
d_I'8322'_560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_560 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_560 v2
du_I'8322'_560 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_560 v0
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
               (coe du_p4_502 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_p3_500 (coe v0)) erased)
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
                           (coe du_p5_504 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                 (coe du_p3_500 (coe v0)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_p1_496 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_p5_504 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                   (coe du_p4_502 (coe v0)) erased)
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
                                                            (coe du_p0_494 (coe v0)) erased)
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
                                                                        (coe du_p1_496 (coe v0))
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
                                                                                 du_p0_494 (coe v0))
                                                                              erased)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_582 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_582
du_I'8323'_582 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_582
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
d_push2'45'below_592 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_592 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_push2'45'below_592 v5 v6 v7
du_push2'45'below_592 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_592 v0 v1 v2
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
d_pop2'45'below_624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_624 ~v0 ~v1 ~v2 v3 = du_pop2'45'below_624 v3
du_pop2'45'below_624 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_624 v0
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
d_wrap'45'sum'45'below_642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_642 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_wrap'45'sum'45'below_642 v4 v5
du_wrap'45'sum'45'below_642 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_642 v0 v1
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
d_visit'45'below_676 ::
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
d_visit'45'below_676 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_visit'45'below_676 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_visit'45'below_676 ::
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
du_visit'45'below_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_112 v11
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
             (coe du_push2'45'below_592 (coe v7) (coe v8) (coe v9))
      MAlonzo.Code.Once.Type.C__'8853'__116 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                   du_visit'45'below_676 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11)))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_750 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                         du_visit'45'below_676 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v7) (coe v8)
                         (coe v9) (coe du_recF_746 (coe v11) (coe v12) (coe v5) (coe v10)))
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
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe du_s'60'b_786 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
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
                   du_visit'45'below_676 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                   (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v7)
                   (coe v8) (coe v9)
                   (coe du_recF_790 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe du_s'60'b_786 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_676 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                      (coe addInt (coe (4 :: Integer)) (coe v5))
                      (coe
                         addInt
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11))
                         (coe v6))
                      (coe v7) (coe v8) (coe v9)
                      (coe du_recG_794 (coe v11) (coe v12) (coe v5) (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_746 ::
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
d_recF_746 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_746 v1 v2 v6 v12
du_recF_746 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_746 v0 v1 v2 v3
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
d_recG_750 ::
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
d_recG_750 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_750 v1 v2 v6 v12
du_recG_750 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_750 v0 v1 v2 v3
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
d_room4_782 ::
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
d_room4_782 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_room4_782 v1 v2 v6 v12
du_room4_782 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_782 v0 v1 v2 v3
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
d_s'60'b_786 ::
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
d_s'60'b_786 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_s'60'b_786 v1 v2 v6 v12
du_s'60'b_786 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_786 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_782 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_790 ::
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
d_recF_790 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_790 v1 v2 v6 v12
du_recF_790 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_790 v0 v1 v2 v3
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
d_recG_794 ::
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
d_recG_794 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_794 v1 v2 v6 v12
du_recG_794 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_794 v0 v1 v2 v3
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
d_rebuild'45'below_816 ::
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
d_rebuild'45'below_816 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_rebuild'45'below_816 v0 v1 v2 v5 v6 v8 v9
du_rebuild'45'below_816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_816 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_112 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe du_pop2'45'below_624 (coe v5)
      MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                   du_rebuild'45'below_816 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7)))
                      (coe v4))
                   (coe v5) (coe du_recG_890 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                      (coe (1 :: Integer)) (coe v3))
                   (coe
                      du_wrap'45'sum'45'below_642
                      (coe du_s'60'b_878 (coe v7) (coe v8) (coe v3) (coe v6))
                      (coe du_b'45'ss_882 (coe v7) (coe v8) (coe v3) (coe v6)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                            du_rebuild'45'below_816 (coe v0) (coe v7) (coe v2)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5)
                            (coe du_recF_886 (coe v7) (coe v8) (coe v3) (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                               (coe (0 :: Integer)) (coe v3))
                            (coe
                               du_wrap'45'sum'45'below_642
                               (coe du_s'60'b_878 (coe v7) (coe v8) (coe v3) (coe v6))
                               (coe du_b'45'ss_882 (coe v7) (coe v8) (coe v3) (coe v6)))
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
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                      (coe du_s'60'b_922 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
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
                   du_rebuild'45'below_816 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7))
                      (coe v4))
                   (coe v5) (coe du_recG_946 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                         (coe addInt (coe (2 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe du_b'45's2_930 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe du_s'60'b_922 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
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
                         du_rebuild'45'below_816 (coe v0) (coe v7) (coe v2)
                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v5)
                         (coe du_recF_942 (coe v7) (coe v8) (coe v3) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe du_b'45'ss_926 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                  (coe du_b'45's3_936 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                        (coe du_b'45'ss_926 (coe v7) (coe v8) (coe v3) (coe v6))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                              (coe
                                                 du_b'45's2_930 (coe v7) (coe v8) (coe v3) (coe v6))
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
                                                       du_b'45's3_936 (coe v7) (coe v8) (coe v3)
                                                       (coe v6))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_874 ::
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
d_room4_874 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_874 v1 v2 v6 v10
du_room4_874 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_874 v0 v1 v2 v3
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
d_s'60'b_878 ::
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
d_s'60'b_878 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_878 v1 v2 v6 v10
du_s'60'b_878 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_878 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_874 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_882 ::
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
d_b'45'ss_882 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_882 v1 v2 v6 v10
du_b'45'ss_882 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_874 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_886 ::
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
d_recF_886 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_886 v1 v2 v6 v10
du_recF_886 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_886 v0 v1 v2 v3
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
d_recG_890 ::
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
d_recG_890 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_890 v1 v2 v6 v10
du_recG_890 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_890 v0 v1 v2 v3
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
d_room4_918 ::
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
d_room4_918 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_918 v1 v2 v6 v10
du_room4_918 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_918 v0 v1 v2 v3
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
d_s'60'b_922 ::
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
d_s'60'b_922 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_922 v1 v2 v6 v10
du_s'60'b_922 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_922 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_918 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_926 ::
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
d_b'45'ss_926 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_926 v1 v2 v6 v10
du_b'45'ss_926 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_926 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_918 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_930 ::
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
d_b'45's2_930 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's2_930 v1 v2 v6 v10
du_b'45's2_930 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_930 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_918 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_936 ::
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
d_b'45's3_936 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's3_936 v1 v2 v6 v10
du_b'45's3_936 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_936 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_918 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_942 ::
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
d_recF_942 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_942 v1 v2 v6 v10
du_recF_942 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_942 v0 v1 v2 v3
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
d_recG_946 ::
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
d_recG_946 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_946 v1 v2 v6 v10
du_recG_946 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_946 v0 v1 v2 v3
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
d_visit'45'idle_978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_978 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1040 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'branching'45'below_1100 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
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
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
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
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_1138 (coe v1) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
            (coe v0) (coe v1) (coe v3) (coe v4))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
            (coe du_b_1118 (coe v1) (coe v3))
            (coe
               du_cata'45'budget'45'of_82
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
            (coe du_b'8804'b2_1120 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
                  (coe v0) (coe v1) (coe v3) (coe v4))
               (coe du_I'8321''45'all_1198 (coe v0) (coe v1) (coe v3) (coe v4))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_1152 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                  (coe v0) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                  (coe du_b_1118 (coe v1) (coe v3))
                  (coe
                     du_cata'45'budget'45'of_82
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
                  (coe du_b'8804'b2_1120 (coe v1) (coe v3))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                        (coe v0) (coe v3) (coe v4))
                     (coe du_I'8322''45'all_1232 (coe v1) (coe v3))))
               (coe
                  du_cata'45'body'45'below_308 (coe v0)
                  (coe
                     du_cata'45'budget'45'of_82
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
d_b_1118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 -> Integer
d_b_1118 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_b_1118 v1 v3
du_b_1118 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_b_1118 v0 v1
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
d_b'8804'b2_1120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'8804'b2_1120 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_b'8804'b2_1120 v1 v3
du_b'8804'b2_1120 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'8804'b2_1120 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe du_b_1118 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_1124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_1124 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_bnd_1124 v1 v3 v7 v8
du_bnd_1124 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_1124 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe addInt (coe (1 :: Integer)) (coe du_b_1118 (coe v0) (coe v1)))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (coe du_b_1118 (coe v0) (coe v1))
         (addInt (coe (1 :: Integer)) (coe v2)) (4 :: Integer) v3)
-- Once.CCC.Codegen.SlotBudget._.cl<b2
d_cl'60'b2_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b2_1130 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_cl'60'b2_1130 v1 v3
du_cl'60'b2_1130 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b2_1130 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_b_1118 (coe v0) (coe v1))))
      (coe
         du_bnd_1124 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b2
d_k'60'b2_1132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b2_1132 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_k'60'b2_1132 v1 v3
du_k'60'b2_1132 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b2_1132 v0 v1
  = coe
      du_bnd_1124 (coe v0) (coe v1) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b2
d_ev'60'b2_1134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b2_1134 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_ev'60'b2_1134 v1 v3
du_ev'60'b2_1134 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b2_1134 v0 v1
  = coe
      du_bnd_1124 (coe v0) (coe v1) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b2
d_pr'60'b2_1136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b2_1136 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_pr'60'b2_1136 v1 v3
du_pr'60'b2_1136 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b2_1136 v0 v1
  = coe
      du_bnd_1124 (coe v0) (coe v1) (coe (3 :: Integer))
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
d_setup_1138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1138 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_setup_1138 v1 v3
du_setup_1138 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1138 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_ev'60'b2_1134 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe du_k'60'b2_1132 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_pr'60'b2_1136 (coe v0) (coe v1)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe du_ev'60'b2_1134 (coe v0) (coe v1)) erased)
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
                                       (coe du_cl'60'b2_1130 (coe v0) (coe v1)) erased)
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
                                                         (coe du_k'60'b2_1132 (coe v0) (coe v1))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1152 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_call_1152 v1 v3
du_call_1152 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1152 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe du_k'60'b2_1132 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
               (coe du_pr'60'b2_1136 (coe v0) (coe v1)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_k'60'b2_1132 (coe v0) (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                           (coe du_cl'60'b2_1130 (coe v0) (coe v1)) erased)
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
                                    (coe du_pr'60'b2_1136 (coe v0) (coe v1)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1164 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7_1164 v1 v3
du_fixed7_1164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1164 v0 v1
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
d_fixed7''_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1166 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7''_1166 v1 v3
du_fixed7''_1166 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1166 v0 v1 = coe du_fixed7_1164 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1170 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q0_1170 v1 v3
du_q0_1170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1170 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1172 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q1_1172 v1 v3
du_q1_1172 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1172 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1174 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q2_1174 v1 v3
du_q2_1174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1174 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1178 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q3_1178 v1 v3
du_q3_1178 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1178 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1182 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q4_1182 v1 v3
du_q4_1182 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1182 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1186 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q5_1186 v1 v3
du_q5_1186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1186 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1190 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q6_1190 v1 v3
du_q6_1190 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1190 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1166 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1194 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_walk'45'room_1194 v1 v3
du_walk'45'room_1194 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1194 v0 v1
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
d_I'8321''45'idle_1196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1196 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1198 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_I'8321''45'all_1198 v0 v1 v3 v4
du_I'8321''45'all_1198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1198 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
               (coe du_q3_1178 (coe v1) (coe v2)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                     (coe du_q6_1190 (coe v1) (coe v2)) erased)
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
                                 (coe du_q6_1190 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_q1_1172 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                       (coe du_q6_1190 (coe v1) (coe v2)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                          (coe du_q2_1174 (coe v1) (coe v2)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_q6_1190 (coe v1) (coe v2)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                (coe du_q0_1170 (coe v1) (coe v2)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                   (coe du_q3_1178 (coe v1) (coe v2)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            du_push2'45'below_592 (coe du_q0_1170 (coe v1) (coe v2))
            (coe du_q4_1182 (coe v1) (coe v2))
            (coe du_q5_1186 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                     (coe du_q0_1170 (coe v1) (coe v2)) erased)
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
                                 (coe du_q0_1170 (coe v1) (coe v2)) erased)
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
                                          (coe du_q3_1178 (coe v1) (coe v2)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                             (coe du_q3_1178 (coe v1) (coe v2)) erased)
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
                  du_push2'45'below_592 (coe du_q1_1172 (coe v1) (coe v2))
                  (coe du_q4_1182 (coe v1) (coe v2))
                  (coe du_q5_1186 (coe v1) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe du_q3_1178 (coe v1) (coe v2)) erased)
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
                        du_visit'45'below_676 (coe v0) (coe v1) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3))
                        (coe du_q0_1170 (coe v1) (coe v2))
                        (coe du_q4_1182 (coe v1) (coe v2))
                        (coe du_q5_1186 (coe v1) (coe v2))
                        (coe du_walk'45'room_1194 (coe v1) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                    (coe du_q1_1172 (coe v1) (coe v2)) erased)
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
                                                (coe du_q1_1172 (coe v1) (coe v2)) erased)
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
                                 du_rebuild'45'below_816 (coe v0) (coe v1)
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
                                 (coe du_q2_1174 (coe v1) (coe v2))
                                 (coe du_walk'45'room_1194 (coe v1) (coe v2)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1232 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_I'8322''45'all_1232 v1 v3
du_I'8322''45'all_1232 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1232 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_592 (coe du_q2_1174 (coe v0) (coe v1))
         (coe du_q4_1182 (coe v0) (coe v1))
         (coe du_q5_1186 (coe v0) (coe v1)))
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
                  (coe du_q2_1174 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_cata'45'slots'45'below_1246 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             d_cata'45'const'45'below_328 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             d_cata'45'nat'45'below_390 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             d_cata'45'linear'45'below_476 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             d_cata'45'branching'45'below_1100 (coe v0) (coe v7) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.resuspend-mono
d_resuspend'45'mono_1302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_resuspend'45'mono_1302 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          d_resuspend'45'mono_1302 (coe v0)
                          (coe addInt (coe (3 :: Integer)) (coe v1))
                          (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                          (coe v11) (coe v9))
                       (coe
                          d_resuspend'45'mono_1302 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                   (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                   (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          d_resuspend'45'mono_1302 (coe v0)
                          (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                          (coe v4) (coe v11) (coe v9))
                       (coe
                          d_resuspend'45'mono_1302 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                (coe v3) (coe v4) (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                   (coe v3) (coe v4) (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.resuspend-below
d_resuspend'45'below_1356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_resuspend'45'below_1356 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v9
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v9))))
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
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe MAlonzo.Code.Once.IRTy.C_Id_10) (coe v6))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                   (coe du_n0_1386 (coe v1)) erased)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                         (coe du_n1_1384 (coe v1)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                            (coe du_e'60'B_1388 (coe v1) (coe v7)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                  (coe du_n1_1384 (coe v1)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                        (coe du_n0_1386 (coe v1)) erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                              (coe du_n1_1384 (coe v1)) erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                 (coe du_n2_1382 (coe v1)) erased)
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
                                                             addInt (coe (4 :: Integer)) (coe v1)))
                                                       erased)
                                                    (coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                                             (coe du_n2_1382 (coe v1)) erased)
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
                                                                            (coe
                                                                               addInt
                                                                               (coe (4 :: Integer))
                                                                               (coe v1)))
                                                                         erased)
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v12 v13
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                          (coe v1))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                   (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                          (coe
                             du_n'60'B_1496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v12) (coe v13) (coe v10) (coe v11))
                          erased)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                du_n'60'B_1496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v12) (coe v13) (coe v10) (coe v11))
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
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
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
                                            du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v12) (coe v10))
                                         (coe
                                            du_l2_1486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v12) (coe v10))
                                         (coe v3) (coe v4) (coe v13) (coe v11))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                         (coe (2 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                            (coe addInt (coe (1 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                  (coe addInt (coe (2 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                        (coe (1 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v1)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                       (coe
                          du_arm_1506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                          (coe v13) (coe v10) (coe v11) (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0)
                                   (coe
                                      du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v12) (coe v10))
                                   (coe
                                      du_l2_1486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v12) (coe v10))
                                   (coe v3) (coe v4) (coe v13) (coe v11))))
                          (coe
                             d_resuspend'45'below_1356 (coe v0)
                             (coe
                                du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                                (coe v10))
                             (coe
                                du_l2_1486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                                (coe v10))
                             (coe v3) (coe v4) (coe v13) (coe v11)
                             (coe
                                du_e'60'n2_1500 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v12) (coe v10) (coe v7))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v2)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                   (coe v1))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
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
                                               (coe v4) (coe v12) (coe v10))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                               (coe (2 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                        (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                              (coe (0 :: Integer)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                             (coe
                                du_arm_1506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                                (coe v13) (coe v10) (coe v11) (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                         (coe v4) (coe v12) (coe v10))))
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                                   (coe
                                      du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v12) (coe v10))
                                   (coe
                                      du_B_1488 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v12) (coe v13) (coe v10) (coe v11))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
                                            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                            (coe v4) (coe v12) (coe v10))))
                                   (coe
                                      du_mid_1490 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v12) (coe v13) (coe v10) (coe v11))
                                   (coe
                                      d_resuspend'45'below_1356 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1))
                                      (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                      (coe v12) (coe v10) (coe du_e'60'3n_1498 (coe v1) (coe v7)))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v12 v13
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                          (coe v1))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                          (coe
                             du_n'60'B_1440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v12) (coe v13) (coe v10) (coe v11))
                          erased)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                             (coe
                                du_n'60'B_1440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v12) (coe v13) (coe v10) (coe v11))
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
                                (coe v3) (coe v4) (coe v12) (coe v10))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                          (coe
                             du_n2_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                             (coe v10))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                (coe MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v10 v11)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                   (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                   (coe v3) (coe v4) (coe v12) (coe v10))))
                          (coe
                             du_mid_1434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                             (coe v13) (coe v10) (coe v11))
                          (coe
                             d_resuspend'45'below_1356 (coe v0)
                             (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                             (coe v4) (coe v12) (coe v10)
                             (coe du_e'60'3n_1442 (coe v1) (coe v7))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                (coe addInt (coe (2 :: Integer)) (coe v1)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                   (coe (2 :: Integer)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                      (coe addInt (coe (1 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                (coe
                                   du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v12) (coe v13) (coe v10) (coe v11))
                                erased)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                      (coe
                                         du_sn'60'B_1438 (coe v0) (coe v1) (coe v2) (coe v3)
                                         (coe v4) (coe v12) (coe v13) (coe v10) (coe v11))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                            (coe
                                               du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3)
                                               (coe v4) (coe v12) (coe v13) (coe v10) (coe v11))
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
                                                     du_n'60'B_1440 (coe v0) (coe v1) (coe v2)
                                                     (coe v3) (coe v4) (coe v12) (coe v13) (coe v10)
                                                     (coe v11))
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
                                         du_n2_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v12) (coe v10))
                                      (coe
                                         du_l2_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v12) (coe v10))
                                      (coe v3) (coe v4) (coe v13) (coe v11))))
                             (coe
                                d_resuspend'45'below_1356 (coe v0)
                                (coe
                                   du_n2_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                                   (coe v10))
                                (coe
                                   du_l2_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                                   (coe v10))
                                (coe v3) (coe v4) (coe v13) (coe v11)
                                (coe
                                   du_e'60'n2_1444 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v12) (coe v10) (coe v7)))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                      (coe addInt (coe (2 :: Integer)) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                         (coe addInt (coe (1 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                      (coe
                                         du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v12) (coe v13) (coe v10) (coe v11))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                         (coe
                                            du_sn'60'B_1438 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v12) (coe v13) (coe v10) (coe v11))
                                         erased)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                                            (coe
                                               du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3)
                                               (coe v4) (coe v12) (coe v13) (coe v10) (coe v11))
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
                                                     du_sn'60'B_1438 (coe v0) (coe v1) (coe v2)
                                                     (coe v3) (coe v4) (coe v12) (coe v13) (coe v10)
                                                     (coe v11))
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.n2
d_n2_1382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n2_1382 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_n2_1382 v1
du_n2_1382 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n2_1382 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.n1
d_n1_1384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n1_1384 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_n1_1384 v1
du_n1_1384 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n1_1384 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.n0
d_n0_1386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n0_1386 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_n0_1386 v1
du_n0_1386 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n0_1386 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.e<B
d_e'60'B_1388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_e'60'B_1388 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_e'60'B_1388 v1 v5
du_e'60'B_1388 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_e'60'B_1388 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
-- Once.CCC.Codegen.SlotBudget._.n2
d_n2_1428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n2_1428 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_n2_1428 v0 v1 v2 v3 v4 v5 v7
du_n2_1428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_1428 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.SlotBudget._.l2
d_l2_1430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_l2_1430 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_l2_1430 v0 v1 v2 v3 v4 v5 v7
du_l2_1430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_1430 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
            (coe v3) (coe v4) (coe v5) (coe v6)))
-- Once.CCC.Codegen.SlotBudget._.B
d_B_1432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_B_1432 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_B_1432 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_B_1432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_B_1432 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0)
         (coe
            du_n2_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v7))
         (coe
            du_l2_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v7))
         (coe v3) (coe v4) (coe v6) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.mid
d_mid_1434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mid_1434 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_mid_1434 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_mid_1434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mid_1434 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_resuspend'45'mono_1302 (coe v0)
      (coe
         du_n2_1428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v7))
      (coe
         du_l2_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v7))
      (coe v3) (coe v4) (coe v6) (coe v8)
-- Once.CCC.Codegen.SlotBudget._.base
d_base_1436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base_1436 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_base_1436 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_base_1436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base_1436 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_resuspend'45'mono_1302 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v7))
      (coe
         du_mid_1434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.sn<B
d_sn'60'B_1438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'B_1438 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_sn'60'B_1438 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_sn'60'B_1438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'60'B_1438 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe
         du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.n<B
d_n'60'B_1440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'B_1440 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_n'60'B_1440 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_n'60'B_1440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'B_1440 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         du_base_1436 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.e<3n
d_e'60'3n_1442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_e'60'3n_1442 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_e'60'3n_1442 v1 v9
du_e'60'3n_1442 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_e'60'3n_1442 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
-- Once.CCC.Codegen.SlotBudget._.e<n2
d_e'60'n2_1444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_e'60'n2_1444 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9
  = du_e'60'n2_1444 v0 v1 v2 v3 v4 v5 v7 v9
du_e'60'n2_1444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_e'60'n2_1444 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe du_e'60'3n_1442 (coe v1) (coe v7))
      (coe
         d_resuspend'45'mono_1302 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.SlotBudget._.n2
d_n2_1484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n2_1484 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_n2_1484 v0 v1 v2 v3 v4 v5 v7
du_n2_1484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_1484 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v5) (coe v6))
-- Once.CCC.Codegen.SlotBudget._.l2
d_l2_1486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_l2_1486 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_l2_1486 v0 v1 v2 v3 v4 v5 v7
du_l2_1486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_1486 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
            (coe v5) (coe v6)))
-- Once.CCC.Codegen.SlotBudget._.B
d_B_1488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_B_1488 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_B_1488 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_B_1488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_B_1488 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0)
         (coe
            du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v7))
         (coe
            du_l2_1486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v7))
         (coe v3) (coe v4) (coe v6) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.mid
d_mid_1490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mid_1490 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_mid_1490 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_mid_1490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mid_1490 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_resuspend'45'mono_1302 (coe v0)
      (coe
         du_n2_1484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v7))
      (coe
         du_l2_1486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v7))
      (coe v3) (coe v4) (coe v6) (coe v8)
-- Once.CCC.Codegen.SlotBudget._.base
d_base_1492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base_1492 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_base_1492 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_base_1492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base_1492 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_resuspend'45'mono_1302 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v5) (coe v7))
      (coe
         du_mid_1490 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.sn<B
d_sn'60'B_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'B_1494 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_sn'60'B_1494 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_sn'60'B_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'60'B_1494 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe
         du_base_1492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.n<B
d_n'60'B_1496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'B_1496 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_n'60'B_1496 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_n'60'B_1496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'B_1496 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         du_base_1492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.SlotBudget._.e<3n
d_e'60'3n_1498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_e'60'3n_1498 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_e'60'3n_1498 v1 v9
du_e'60'3n_1498 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_e'60'3n_1498 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
-- Once.CCC.Codegen.SlotBudget._.e<n2
d_e'60'n2_1500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_e'60'n2_1500 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9
  = du_e'60'n2_1500 v0 v1 v2 v3 v4 v5 v7 v9
du_e'60'n2_1500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_e'60'n2_1500 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe du_e'60'3n_1498 (coe v1) (coe v7))
      (coe
         d_resuspend'45'mono_1302 (coe v0)
         (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v5) (coe v6))
-- Once.CCC.Codegen.SlotBudget._.arm
d_arm_1506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_arm_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 v12
  = du_arm_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_arm_1506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
du_arm_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
            (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
            (coe
               du_n'60'B_1496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8))
            erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
         (coe v10) (coe v11)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe addInt (coe (1 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe addInt (coe (2 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                    (coe v9))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                  (coe
                     du_base_1492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                     (coe v6) (coe v7) (coe v8))
                  erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                        (coe
                           du_sn'60'B_1494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v6) (coe v7) (coe v8))
                        erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'slot_74
                              (coe
                                 du_base_1492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                 (coe v6) (coe v7) (coe v8))
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
                                             du_sn'60'B_1494 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget.sigop-below
d_sigop'45'below_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_sigop'45'below_1536 ~v0 v1 v2 v3 v4 v5
  = du_sigop'45'below_1536 v1 v2 v3 v4 v5
du_sigop'45'below_1536 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
du_sigop'45'below_1536 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'code_512
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
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
                            (coe addInt (coe (1 :: Integer)) (coe v3)))
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
                                  (coe addInt (coe (2 :: Integer)) (coe v3)))
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
                                        (coe addInt (coe (1 :: Integer)) (coe v3)))
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
                                                    (coe addInt (coe (2 :: Integer)) (coe v3)))
                                                 erased)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'code_512
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_1564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegOK_514
d_slots'45'below_1564 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_budget'45'of_74
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10)))
                (coe
                   du_trace'45'of_78
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   d_frontier'45'mono_156 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
                (coe
                   d_slots'45'below_1564 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                   (coe v5)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_1564 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
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
                                   d_h_1606 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9) (coe v10)
                                   (coe v4) (coe v5)))
                             erased)
                          (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                       (coe
                          du_trace'45'of_78
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             du_budget'45'of_74
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10)))
                          (coe
                             du_trace'45'of_78
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             d_frontier'45'mono_156 (coe v0) (coe v1) (coe v12) (coe v10)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                   (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                      (coe v9)))))
                          (coe
                             d_slots'45'below_1564 (coe v0) (coe v1) (coe v11) (coe v9)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
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
                                      d_h_1606 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
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
                                         d_h_1606 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                         (coe v10) (coe v4) (coe v5)))
                                   erased)
                                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                             (coe
                                du_trace'45'of_78
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                   (coe v0) (coe v1) (coe v12)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                            (coe v0) (coe v1) (coe v11)
                                            (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                            (coe v9))))
                                   (coe v10)))
                             (coe
                                d_slots'45'below_1564 (coe v0) (coe v1) (coe v12) (coe v10)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                         (coe (2 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                            (coe addInt (coe (3 :: Integer)) (coe v4)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
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
                                            d_h_1606 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
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
                                               d_h_1606 (coe v0) (coe v1) (coe v11) (coe v12)
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
                                                        d_h_1606 (coe v0) (coe v1) (coe v11)
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
                                                              d_h_1606 (coe v0) (coe v1) (coe v11)
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
                                                                 d_h_1606 (coe v0) (coe v1)
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                          du_trace'45'of_78
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                             (coe v0) (coe v12) (coe v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                             (coe v10)))
                       (coe
                          d_slots'45'below_1564 (coe v0) (coe v12) (coe v2) (coe v10)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
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
                                du_trace'45'of_78
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   du_budget'45'of_74
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                      (coe MAlonzo.Code.Once.IR.C_case_68 v9 v10)))
                                (coe
                                   du_trace'45'of_78
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   d_frontier'45'mono_156 (coe v0) (coe v12) (coe v2) (coe v10)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                         (coe v0) (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                            (coe v0) (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                                (coe
                                   d_slots'45'below_1564 (coe v0) (coe v11) (coe v2) (coe v9)
                                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5))))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
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
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_terminal_72)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                              du_trace'45'of_78
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                           d_cata'45'slots'45'below_1246 (coe v0)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v13)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10)))))
                           (coe
                              d_slots'45'below_1564 (coe v0)
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_122 v7 v10)))
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
      MAlonzo.Code.Once.IR.C_const_126 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_520
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_126 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_522
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
                    (coe
                       du_trace'45'of_78
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_126 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_132 v6 v7 v8
        -> coe
             du_sigop'45'below_1536 (coe v6) (coe v7) (coe v8) (coe v4)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v8)))
      MAlonzo.Code.Once.IR.C_Call_138 v8
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'idle_542
             (coe
                du_trace'45'of_78
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Call_138 v8)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1606 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_156 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_156 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_74
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget.bodies-of
d_bodies'45'of_1750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bodies'45'of_1750 ~v0 v1 = du_bodies'45'of_1750 v1
du_bodies'45'of_1750 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bodies'45'of_1750 v0
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
d_blocks'45'below_1764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'below_1764 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_bodies'45'of_1750
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                d_blocks'45'below_1764 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_blocks'45'below_1764 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bodies'45'of_1750
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                          (coe v0) (coe v1) (coe v11)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                    (coe
                       d_blocks'45'below_1764 (coe v0) (coe v1) (coe v11) (coe v9)
                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       d_blocks'45'below_1764 (coe v0) (coe v1) (coe v12) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                       du_bodies'45'of_1750
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                          (coe v0) (coe v11) (coe v2) (coe v4)
                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                    (coe
                       d_blocks'45'below_1764 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_blocks'45'below_1764 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
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
                    (d_slots'45'below_1564
                       (coe v0)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                       (coe v11) (coe v9) (coe (0 :: Integer))
                       (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (d_blocks'45'below_1764
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
                           d_blocks'45'below_1764 (coe v0)
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
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v13
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45'pre_620
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                       (coe (0 :: Integer)))
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
                                             du_0'60'cb_1866 (coe v0) (coe v13) (coe v11) (coe v12)
                                             (coe v10) (coe v5))
                                          (coe
                                             du_mono_1868 (coe v0) (coe v13) (coe v7) (coe v11)
                                             (coe v12) (coe v10) (coe v5)))
                                       erased)
                                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_segok'45''43''43'_580
                                 (coe
                                    du_trace'45'of_78
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                       (coe v0) (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                          (coe v12))
                                       (coe (1 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v10)))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_segok'45'weaken_608
                                    (coe
                                       du_cb_1864 (coe v0) (coe v13) (coe v11) (coe v12) (coe v10)
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                                (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v5))
                                                (coe v10)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                                   (coe v0) (coe v1)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                      (coe v13) (coe v12))
                                                   (coe (1 :: Integer))
                                                   (coe addInt (coe (1 :: Integer)) (coe v5))
                                                   (coe v10))))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))
                                          (coe (0 :: Integer)) (coe v13) (coe v7)))
                                    (coe
                                       du_trace'45'of_78
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                          (coe v0) (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                             (coe v12))
                                          (coe (1 :: Integer))
                                          (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v10)))
                                    (coe
                                       du_mono_1868 (coe v0) (coe v13) (coe v7) (coe v11) (coe v12)
                                       (coe v10) (coe v5))
                                    (coe
                                       d_slots'45'below_1564 (coe v0) (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                          (coe v12))
                                       (coe v10) (coe (1 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v5))))
                                 (coe
                                    d_resuspend'45'below_1356 (coe v0)
                                    (coe
                                       du_cb_1864 (coe v0) (coe v13) (coe v11) (coe v12) (coe v10)
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                             (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                (coe v13) (coe v12))
                                             (coe (1 :: Integer))
                                             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v10))))
                                    (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v5))
                                    (coe (0 :: Integer)) (coe v13) (coe v7)
                                    (coe
                                       du_0'60'cb_1866 (coe v0) (coe v13) (coe v11) (coe v12)
                                       (coe v10) (coe v5)))))
                           (d_blocks'45'below_1764
                              (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13) (coe v12))
                              (coe v10) (coe (1 :: Integer))
                              (coe addInt (coe (1 :: Integer)) (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_126 v7 v8
        -> coe
             seq (coe v7)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_SigOp_132 v6 v7 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Call_138 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.cb
d_cb_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer -> Integer
d_cb_1864 v0 v1 ~v2 v3 v4 v5 ~v6 v7 = du_cb_1864 v0 v1 v3 v4 v5 v7
du_cb_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer
du_cb_1864 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v1) (coe v3))
         (coe (1 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v5))
         (coe v4))
-- Once.CCC.Codegen.SlotBudget._.0<cb
d_0'60'cb_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'cb_1866 v0 v1 ~v2 v3 v4 v5 ~v6 v7
  = du_0'60'cb_1866 v0 v1 v3 v4 v5 v7
du_0'60'cb_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'cb_1866 v0 v1 v2 v3 v4 v5
  = coe
      d_frontier'45'mono_156 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v1) (coe v3))
      (coe v4) (coe (1 :: Integer))
      (coe addInt (coe (1 :: Integer)) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.mono
d_mono_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mono_1868 v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_mono_1868 v0 v1 v2 v3 v4 v5 v7
du_mono_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mono_1868 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_resuspend'45'mono_1302 (coe v0)
      (coe
         du_cb_1864 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v1) (coe v4))
               (coe (1 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v6))
               (coe v5))))
      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))
      (coe (0 :: Integer)) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-all
d_ir'45'slots'45'below'45'all_1894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'all_1894 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_78
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1564
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
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
                  (coe v0) (coe v1) (coe v2) (coe v3))
               (coe
                  du_bodies'45'of_1750
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                     (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                     (coe (0 :: Integer)) (coe v3)))
               (coe
                  d_blocks'45'below_1764 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe (0 :: Integer)) (coe (0 :: Integer))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.SlotBudget.emitted-slot-seg
d_emitted'45'slot'45'seg_1912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_1912 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_emitted'45'slot'45'seg_1912 v0 v1 v2 v3 v4 v6
du_emitted'45'slot'45'seg_1912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_1912 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_below_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45'at_980
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_860
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4)
         (coe
            d_ir'45'slots'45'below'45'all_1894 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      v5 erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-under-lab
d_ir'45'slots'45'below'45'under'45'lab_1936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'under'45'lab_1936 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_78
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer)) (coe v4) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1564
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
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
                           (coe v0) (coe v1) (coe v2) (coe v4) (coe v3))
                        (coe v5))))
               (coe
                  du_bodies'45'of_1750
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                     (coe v0) (coe v1) (coe v2) (coe (0 :: Integer)) (coe v4) (coe v3)))
               (coe
                  d_blocks'45'below_1764 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe (0 :: Integer)) (coe v4)))
            (MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_saved_152
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_pop'45'with_170 (coe v5)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_mkSeg_154
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
                        (coe v0) (coe v1) (coe v2) (coe v4) (coe v3))
                     (coe v5))))))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold-lab
d_ir'45'seg'45'fold'45'lab_1956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold'45'lab_1956 = erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-top
d_ir'45'slots'45'below'45'top_1974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'top_1974 v0 v1 v2 v3 ~v4 v5
  = du_ir'45'slots'45'below'45'top_1974 v0 v1 v2 v3 v5
du_ir'45'slots'45'below'45'top_1974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
du_ir'45'slots'45'below'45'top_1974 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
      (coe
         du_trace'45'of_78
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_ok'45'all_530
         (d_slots'45'below_1564
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
                     (coe v0) (coe v1) (coe v2) (coe v3))
                  (coe
                     du_bodies'45'of_1750
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                        (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                        (coe (0 :: Integer)) (coe v3)))
                  (coe
                     d_blocks'45'below_1764 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe (0 :: Integer)) (coe (0 :: Integer))))
               v4)))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold-top
d_ir'45'seg'45'fold'45'top_1994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold'45'top_1994 = erased
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-under
d_ir'45'slots'45'below'45'under_2010 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_ir'45'slots'45'below'45'under_2010 v0 v1 v2 v3
  = coe
      d_ir'45'slots'45'below'45'under'45'lab_1936 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe (0 :: Integer))
-- Once.CCC.Codegen.SlotBudget.ir-seg-fold
d_ir'45'seg'45'fold_2022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'seg'45'fold_2022 = erased
