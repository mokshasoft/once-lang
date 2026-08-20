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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_cata'45'br'45'I'8321'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_320
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₂
d_cata'45'br'45'I'8322'_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_cata'45'br'45'I'8322'_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_328
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-dispatch
d_cata'45'dispatch_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.fsize
d_fsize_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
d_fsize_32 ~v0 = du_fsize_32
du_fsize_32 :: MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
du_fsize_32
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget
d_ir'45'stack'45'budget_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_34 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_750
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace
d_ir'45'to'45'trace_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_ir'45'to'45'trace_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_732
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace'
d_ir'45'to'45'trace''_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_38 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.pop2
d_pop2_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_pop2_42 ~v0 = du_pop2_42
du_pop2_42 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
du_pop2_42
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_176
-- Once.CCC.Codegen.SlotBudget._.push2
d_push2_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_push2_44 ~v0 = du_push2_44
du_push2_44 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
du_push2_44
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
-- Once.CCC.Codegen.SlotBudget._.rebuild-walk
d_rebuild'45'walk_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_rebuild'45'walk_46 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.SlotBudget._.visit-walk
d_visit'45'walk_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_visit'45'walk_56 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.wrap-sum
d_wrap'45'sum_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_wrap'45'sum_58 ~v0 = du_wrap'45'sum_58
du_wrap'45'sum_58 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
du_wrap'45'sum_58
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_70 ~v0 v1 = du_budget'45'of_70 v1
du_budget'45'of_70 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_70 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_trace'45'of_74 ~v0 v1 = du_trace'45'of_74 v1
du_trace'45'of_74 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
du_trace'45'of_74 v0
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
d_cata'45'budget'45'of_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_78 ~v0 v1 = du_cata'45'budget'45'of_78 v1
du_cata'45'budget'45'of_78 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'budget'45'of_78 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_cata'45'trace'45'of_82 ~v0 v1 = du_cata'45'trace'45'of_82 v1
du_cata'45'trace'45'of_82 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
du_cata'45'trace'45'of_82 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow
d_SlotBelow_90 a0 a1 a2 = ()
data T_SlotBelow_90
  = C_mkSlotBelow_112 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.SlotBudget.SlotBelow.below
d_below_106 ::
  T_SlotBelow_90 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_106 v0
  = case coe v0 of
      C_mkSlotBelow_112 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow.pair-below
d_pair'45'below_110 ::
  T_SlotBelow_90 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pair'45'below_110 v0
  = case coe v0 of
      C_mkSlotBelow_112 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-none
d_sb'45'none_118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_90
d_sb'45'none_118 ~v0 ~v1 ~v2 ~v3 = du_sb'45'none_118
du_sb'45'none_118 :: T_SlotBelow_90
du_sb'45'none_118
  = coe
      C_mkSlotBelow_112 (coe (\ v0 v1 -> coe du_go_134))
      (coe (\ v0 v1 -> coe du_go_134))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_go_134
du_go_134 :: AgdaAny
du_go_134 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-slot
d_sb'45'slot_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_90
d_sb'45'slot_152 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_sb'45'slot_152 v5 v6
du_sb'45'slot_152 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_90
du_sb'45'slot_152 v0 v1
  = coe C_mkSlotBelow_112 (coe (\ v2 v3 -> v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.just-inj
d_just'45'inj_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_170 = erased
-- Once.CCC.Codegen.SlotBudget.sb-weaken
d_sb'45'weaken_184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_184 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sb'45'weaken_184 v3 v4 v5
du_sb'45'weaken_184 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sb'45'weaken_184 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       C_mkSlotBelow_112
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_below_106 v5 v9 erased) (coe v1)))
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_pair'45'below_110 v5 v9 erased) (coe v1))))
                    (coe du_sb'45'weaken_184 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-le
d_sb'45'le_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_90 -> T_SlotBelow_90
d_sb'45'le_208 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sb'45'le_208 v4 v5
du_sb'45'le_208 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_90 -> T_SlotBelow_90
du_sb'45'le_208 v0 v1
  = coe
      C_mkSlotBelow_112
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_below_106 v1 v2 erased) (coe v0)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_pair'45'below_110 v1 v2 erased) (coe v0)))
-- Once.CCC.Codegen.SlotBudget.SegState
d_SegState_222 a0 = ()
data T_SegState_222 = C_mkSeg_232 Integer [Integer]
-- Once.CCC.Codegen.SlotBudget.SegState.cur
d_cur_228 :: T_SegState_222 -> Integer
d_cur_228 v0
  = case coe v0 of
      C_mkSeg_232 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegState.saved
d_saved_230 :: T_SegState_222 -> [Integer]
d_saved_230 v0
  = case coe v0 of
      C_mkSeg_232 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegAction
d_SegAction_234 a0 = ()
data T_SegAction_234
  = C_seg'45'id_236 | C_seg'45'push_238 Integer | C_seg'45'pop_240
-- Once.CCC.Codegen.SlotBudget.seg-action
d_seg'45'action_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_SegAction_234
d_seg'45'action_242 ~v0 v1 = du_seg'45'action_242 v1
du_seg'45'action_242 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_SegAction_234
du_seg'45'action_242 v0
  = let v1 = coe C_seg'45'id_236 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2208 v3 v4
                  -> coe C_seg'45'push_238 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2210 v3
                  -> coe C_seg'45'pop_240
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotBudget.pop-with
d_pop'45'with_246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SegState_222 -> T_SegState_222
d_pop'45'with_246 ~v0 v1 v2 = du_pop'45'with_246 v1 v2
du_pop'45'with_246 :: [Integer] -> T_SegState_222 -> T_SegState_222
du_pop'45'with_246 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_232 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply
d_seg'45'apply_254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_234 -> T_SegState_222 -> T_SegState_222
d_seg'45'apply_254 ~v0 v1 v2 = du_seg'45'apply_254 v1 v2
du_seg'45'apply_254 ::
  T_SegAction_234 -> T_SegState_222 -> T_SegState_222
du_seg'45'apply_254 v0 v1
  = case coe v0 of
      C_seg'45'id_236 -> coe v1
      C_seg'45'push_238 v2
        -> coe
             C_mkSeg_232 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_228 (coe v1)) (coe d_saved_230 (coe v1)))
      C_seg'45'pop_240
        -> coe du_pop'45'with_246 (coe d_saved_230 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-step
d_seg'45'step_264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_SegState_222 -> T_SegState_222
d_seg'45'step_264 ~v0 v1 v2 = du_seg'45'step_264 v1 v2
du_seg'45'step_264 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_SegState_222 -> T_SegState_222
du_seg'45'step_264 v0 v1
  = coe
      du_seg'45'apply_254 (coe du_seg'45'action_242 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget.seg-fold
d_seg'45'fold_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegState_222 -> T_SegState_222
d_seg'45'fold_270 ~v0 v1 v2 = du_seg'45'fold_270 v1 v2
du_seg'45'fold_270 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegState_222 -> T_SegState_222
du_seg'45'fold_270 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_seg'45'fold_270 (coe v3)
             (coe du_seg'45'step_264 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-fold-++
d_seg'45'fold'45''43''43'_286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_286 = erased
-- Once.CCC.Codegen.SlotBudget.AllSeg
d_AllSeg_300 a0 a1 a2 = ()
data T_AllSeg_300
  = C_'91''93'_304 | C__'8759'__312 T_SlotBelow_90 T_AllSeg_300
-- Once.CCC.Codegen.SlotBudget.allseg-++
d_allseg'45''43''43'_320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_222 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_AllSeg_300 -> T_AllSeg_300 -> T_AllSeg_300
d_allseg'45''43''43'_320 ~v0 ~v1 v2 ~v3 v4 v5
  = du_allseg'45''43''43'_320 v2 v4 v5
du_allseg'45''43''43'_320 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_AllSeg_300 -> T_AllSeg_300 -> T_AllSeg_300
du_allseg'45''43''43'_320 v0 v1 v2
  = case coe v1 of
      C_'91''93'_304 -> coe v2
      C__'8759'__312 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__312 v6
                    (coe du_allseg'45''43''43'_320 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.allseg-++bal
d_allseg'45''43''43'bal_336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_222 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_300 -> T_AllSeg_300 -> T_AllSeg_300
d_allseg'45''43''43'bal_336 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_allseg'45''43''43'bal_336 v2 v5 v6
du_allseg'45''43''43'bal_336 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_AllSeg_300 -> T_AllSeg_300 -> T_AllSeg_300
du_allseg'45''43''43'bal_336 v0 v1 v2
  = coe du_allseg'45''43''43'_320 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotBudget.SavedLE
d_SavedLE_346 a0 a1 a2 = ()
data T_SavedLE_346
  = C_'91''93'_348 |
    C__'8759'__358 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_346
-- Once.CCC.Codegen.SlotBudget.SegLE
d_SegLE_364 a0 a1 a2 = ()
data T_SegLE_364
  = C_mkSegLE_378 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_346
-- Once.CCC.Codegen.SlotBudget.SegLE.cur-le
d_cur'45'le_374 ::
  T_SegLE_364 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_374 v0
  = case coe v0 of
      C_mkSegLE_378 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegLE.saved-le
d_saved'45'le_376 :: T_SegLE_364 -> T_SavedLE_346
d_saved'45'le_376 v0
  = case coe v0 of
      C_mkSegLE_378 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.saved-le-refl
d_saved'45'le'45'refl_382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SavedLE_346
d_saved'45'le'45'refl_382 ~v0 v1 = du_saved'45'le'45'refl_382 v1
du_saved'45'le'45'refl_382 :: [Integer] -> T_SavedLE_346
du_saved'45'le'45'refl_382 v0
  = case coe v0 of
      [] -> coe C_'91''93'_348
      (:) v1 v2
        -> coe
             C__'8759'__358
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (coe du_saved'45'le'45'refl_382 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.pop-mono
d_pop'45'mono_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_222 ->
  T_SegState_222 ->
  [Integer] ->
  [Integer] -> T_SavedLE_346 -> T_SegLE_364 -> T_SegLE_364
d_pop'45'mono_396 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pop'45'mono_396 v3 v4 v5 v6
du_pop'45'mono_396 ::
  [Integer] ->
  [Integer] -> T_SavedLE_346 -> T_SegLE_364 -> T_SegLE_364
du_pop'45'mono_396 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__358 v10 v11 -> coe C_mkSegLE_378 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply-mono
d_seg'45'apply'45'mono_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_234 ->
  T_SegState_222 -> T_SegState_222 -> T_SegLE_364 -> T_SegLE_364
d_seg'45'apply'45'mono_418 ~v0 v1 v2 v3 v4
  = du_seg'45'apply'45'mono_418 v1 v2 v3 v4
du_seg'45'apply'45'mono_418 ::
  T_SegAction_234 ->
  T_SegState_222 -> T_SegState_222 -> T_SegLE_364 -> T_SegLE_364
du_seg'45'apply'45'mono_418 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_236 -> coe v3
      C_seg'45'push_238 v4
        -> coe
             C_mkSegLE_378
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_228 (coe du_seg'45'apply_254 (coe v0) (coe v1))))
             (coe
                C__'8759'__358 (d_cur'45'le_374 (coe v3))
                (d_saved'45'le_376 (coe v3)))
      C_seg'45'pop_240
        -> coe
             du_pop'45'mono_396 (coe d_saved_230 (coe v1))
             (coe d_saved_230 (coe v2)) (coe d_saved'45'le_376 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken
d_seg'45'weaken_438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_222 ->
  T_SegState_222 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegLE_364 -> T_AllSeg_300 -> T_AllSeg_300
d_seg'45'weaken_438 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken_438 v1 v2 v3 v4 v5
du_seg'45'weaken_438 ::
  T_SegState_222 ->
  T_SegState_222 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegLE_364 -> T_AllSeg_300 -> T_AllSeg_300
du_seg'45'weaken_438 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_304 -> coe C_'91''93'_304
      C__'8759'__312 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__312
                    (coe du_sb'45'le_208 (coe d_cur'45'le_374 (coe v3)) (coe v8))
                    (coe
                       du_seg'45'weaken_438
                       (coe
                          du_seg'45'apply_254 (coe du_seg'45'action_242 (coe v10)) (coe v0))
                       (coe du_seg'45'step_264 (coe v10) (coe v1)) (coe v11)
                       (coe
                          du_seg'45'apply'45'mono_418 (coe du_seg'45'action_242 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken-cur
d_seg'45'weaken'45'cur_458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_300 -> T_AllSeg_300
d_seg'45'weaken'45'cur_458 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken'45'cur_458 v1 v2 v3 v4 v5
du_seg'45'weaken'45'cur_458 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_300 -> T_AllSeg_300
du_seg'45'weaken'45'cur_458 v0 v1 v2 v3 v4
  = coe
      du_seg'45'weaken_438 (coe C_mkSeg_232 (coe v0) (coe v2))
      (coe C_mkSeg_232 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_378 (coe v4) (coe du_saved'45'le'45'refl_382 (coe v2)))
-- Once.CCC.Codegen.SlotBudget.is-id?
d_is'45'id'63'_464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_234 -> Bool
d_is'45'id'63'_464 ~v0 v1 = du_is'45'id'63'_464 v1
du_is'45'id'63'_464 :: T_SegAction_234 -> Bool
du_is'45'id'63'_464 v0
  = case coe v0 of
      C_seg'45'id_236 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_238 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_240 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-idle?
d_seg'45'idle'63'_466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] -> Bool
d_seg'45'idle'63'_466 ~v0 v1 = du_seg'45'idle'63'_466 v1
du_seg'45'idle'63'_466 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] -> Bool
du_seg'45'idle'63'_466 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe du_is'45'id'63'_464 (coe du_seg'45'action_242 (coe v1)))
             (coe du_seg'45'idle'63'_466 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.idle-step
d_idle'45'step_476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_476 = erased
-- Once.CCC.Codegen.SlotBudget._.go
d_go_490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_222 ->
  T_SegAction_234 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_490 = erased
-- Once.CCC.Codegen.SlotBudget.idle-head
d_idle'45'head_496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_496 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-fst
d_'8743''45'fst_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_512 = erased
-- Once.CCC.Codegen.SlotBudget.idle-tail
d_idle'45'tail_522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_522 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-snd
d_'8743''45'snd_538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_538 = erased
-- Once.CCC.Codegen.SlotBudget.idle-++
d_idle'45''43''43'_550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_550 = erased
-- Once.CCC.Codegen.SlotBudget.idle-neutral
d_idle'45'neutral_574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_574 = erased
-- Once.CCC.Codegen.SlotBudget.SegOK
d_SegOK_590 a0 a1 a2 = ()
newtype T_SegOK_590 = C_mkSegOK_612 ([Integer] -> T_AllSeg_300)
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-all
d_ok'45'all_606 :: T_SegOK_590 -> [Integer] -> T_AllSeg_300
d_ok'45'all_606 v0
  = case coe v0 of
      C_mkSegOK_612 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-neu
d_ok'45'neu_610 ::
  T_SegOK_590 ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_610 = erased
-- Once.CCC.Codegen.SlotBudget.segok-idle
d_segok'45'idle_618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_590
d_segok'45'idle_618 ~v0 ~v1 v2 ~v3 v4 = du_segok'45'idle_618 v2 v4
du_segok'45'idle_618 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_590
du_segok'45'idle_618 v0 v1
  = coe C_mkSegOK_612 (\ v2 -> coe du_go_634 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_300
d_go_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 = du_go_634 v6 v8
du_go_634 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_300
du_go_634 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_304)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__312 v6 (coe du_go_634 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.segok-++
d_segok'45''43''43'_656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590 -> T_SegOK_590
d_segok'45''43''43'_656 ~v0 ~v1 v2 ~v3 v4 v5
  = du_segok'45''43''43'_656 v2 v4 v5
du_segok'45''43''43'_656 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590 -> T_SegOK_590
du_segok'45''43''43'_656 v0 v1 v2
  = coe
      C_mkSegOK_612
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_336 (coe v0) (coe d_ok'45'all_606 v1 v3)
           (coe d_ok'45'all_606 v2 v3))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 ->
  T_SegOK_590 ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_674 = erased
-- Once.CCC.Codegen.SlotBudget.segok-weaken
d_segok'45'weaken_684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_590 -> T_SegOK_590
d_segok'45'weaken_684 ~v0 v1 v2 v3 v4 v5
  = du_segok'45'weaken_684 v1 v2 v3 v4 v5
du_segok'45'weaken_684 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_590 -> T_SegOK_590
du_segok'45'weaken_684 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_612
      (\ v5 ->
         coe
           du_seg'45'weaken'45'cur_458 v0 v1 v5 v2 v3
           (coe d_ok'45'all_606 v4 v5))
-- Once.CCC.Codegen.SlotBudget.segok-pre
d_segok'45'pre_696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_590 -> T_SegOK_590
d_segok'45'pre_696 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_segok'45'pre_696 v2 v5 v6
du_segok'45'pre_696 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_590 -> T_SegOK_590
du_segok'45'pre_696 v0 v1 v2
  = coe
      du_segok'45''43''43'_656 (coe v0)
      (coe du_segok'45'idle_618 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotBudget.segok-thunk
d_segok'45'thunk_716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_segok'45'thunk_716 ~v0 v1 ~v2 ~v3 ~v4 v5 v6
  = du_segok'45'thunk_716 v1 v5 v6
du_segok'45'thunk_716 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
du_segok'45'thunk_716 v0 v1 v2
  = coe C_mkSegOK_612 (coe du_inner_736 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotBudget._.inner
d_inner_736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> [Integer] -> T_AllSeg_300
d_inner_736 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_inner_736 v1 v5 v6 v7
du_inner_736 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> [Integer] -> T_AllSeg_300
du_inner_736 v0 v1 v2 v3
  = coe
      C__'8759'__312 (coe du_sb'45'none_118)
      (coe
         du_allseg'45''43''43'_320 (coe v1)
         (coe
            d_ok'45'all_606 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__312 (coe du_sb'45'none_118)
            (coe C__'8759'__312 (coe du_sb'45'none_118) (coe C_'91''93'_304))))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_744 = erased
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_758 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_cata'45'mono_758 v1 v3
du_cata'45'mono_758 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_758 v0 v1
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
                      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                      (coe addInt (coe (3 :: Integer)) (coe v1)))))
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
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v2))))
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
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v2))))
                         (coe v1)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.frontier-mono
d_frontier'45'mono_804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_804 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_804 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_frontier'45'mono_804 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   du_budget'45'of_70
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
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
                                    MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                    (coe addInt (coe (2 :: Integer)) (coe v4)))))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 d_frontier'45'mono_804 (coe v0) (coe v1) (coe v12) (coe v9)
                                 (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5))
                              (coe
                                 d_frontier'45'mono_804 (coe v0) (coe v1) (coe v13) (coe v10)
                                 (coe
                                    du_budget'45'of_70
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
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
                                 d_frontier'45'mono_804 (coe v0) (coe v1) (coe v12) (coe v9)
                                 (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                              (coe
                                 d_frontier'45'mono_804 (coe v0) (coe v1) (coe v13) (coe v10)
                                 (coe
                                    du_budget'45'of_70
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v4))))
      MAlonzo.Code.Once.IR.C_inr_62 v8
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v4))))
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_frontier'45'mono_804 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_frontier'45'mono_804 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          du_budget'45'of_70
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> coe
             seq (coe v10)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v4))))
      MAlonzo.Code.Once.IR.C_apply_92
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
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    du_cata'45'mono_758
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10)))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Out_116 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Ana_126 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_const_148 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.lt-refl
d_lt'45'refl_948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_948 ~v0 v1 = du_lt'45'refl_948 v1
du_lt'45'refl_948 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lt'45'refl_948 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_956 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'nat'45'layer'45'below_956 v4 v5
du_cata'45'nat'45'layer'45'below_956 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_956 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_152 (coe v0) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe v1) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_152 (coe v0) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe v1) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-body-below
d_cata'45'body'45'below_986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'body'45'below_986 v0 v1 ~v2 v3 ~v4 v5 v6
  = du_cata'45'body'45'below_986 v0 v1 v3 v5 v6
du_cata'45'body'45'below_986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
du_cata'45'body'45'below_986 v0 v1 v2 v3 v4
  = coe
      du_segok'45'pre_696
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (coe du_segok'45'thunk_716 (coe v1) (coe v3) (coe v4))
-- Once.CCC.Codegen.SlotBudget.cata-const-below
d_cata'45'const'45'below_1006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'const'45'below_1006 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_656
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
               (coe addInt (coe (1 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
      (coe
         du_segok'45'idle_618
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                  (coe addInt (coe (1 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe v2))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                    (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                   (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe du_k'60'b_1026 (coe v2)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_152 (coe du_cl'60'b_1024 (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_152 (coe du_k'60'b_1026 (coe v2)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_152 (coe du_k'60'b_1026 (coe v2))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_152
                                                      (coe du_cl'60'b_1024 (coe v2)) erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_118)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_152
                                                               (coe du_k'60'b_1026 (coe v2)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_118)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_118)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))
      (coe
         du_cata'45'body'45'below_986 (coe v0)
         (coe
            du_cata'45'budget'45'of_78
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
               (coe v0)
               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22)
               (coe v1) (coe v2) (coe v3) (coe v4)))
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.n+2
d_n'43'2_1022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'43'2_1022 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_n'43'2_1022 v2
du_n'43'2_1022 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'43'2_1022 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1024 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1024 v2
du_cl'60'b_1024 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1024 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
      (coe du_n'43'2_1022 (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1026 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1026 v2
du_k'60'b_1026 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1026 v0 = coe du_n'43'2_1022 (coe v0)
-- Once.CCC.Codegen.SlotBudget.cata-nat-below
d_cata'45'nat'45'below_1048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'nat'45'below_1048 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_656
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (2 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (6 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      (coe
         du_segok'45'idle_618
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                  (coe addInt (coe (3 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe addInt (coe (2 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (6 :: Integer)) (coe v3))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
         (coe du_setup_1074 (coe v2)))
      (coe
         du_segok'45''43''43'_656
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0) (coe v3))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v3)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                            (coe (0 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                                                 (coe
                                                                                    (0 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
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
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
         (coe
            du_segok'45'idle_618
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                   (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (3 :: Integer)) (coe v3)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                            (coe v0) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                               (coe v0)
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v3)))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                               (coe (0 :: Integer)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                                           (coe (2 :: Integer)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
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
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
            (coe du_I'8321'_1090 (coe v2)))
         (coe
            du_segok'45''43''43'_656
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                        (coe addInt (coe (2 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
            (coe
               du_segok'45'idle_618
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                           (coe addInt (coe (2 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                    (coe addInt (coe (3 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
               (coe du_call_1082 (coe v2)))
            (coe
               du_segok'45''43''43'_656
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (4 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (5 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                             (coe (1 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
               (coe
                  du_segok'45'idle_618
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (4 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (5 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe v2))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                (coe (1 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
                  (coe du_I'8322'_1100 (coe v2)))
               (coe
                  du_segok'45''43''43'_656
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                              (coe addInt (coe (2 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                  (coe
                     du_segok'45'idle_618
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (2 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                     (coe du_call_1082 (coe v2)))
                  (coe
                     du_segok'45''43''43'_656
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (5 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        du_segok'45'idle_618
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (4 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                          (coe addInt (coe (5 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_1110))
                     (coe
                        du_cata'45'body'45'below_986 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_78
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (7 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> Integer
d_b_1064 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_1064 v2
du_b_1064 :: Integer -> Integer
du_b_1064 v0 = coe addInt (coe (4 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_1066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_1066 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p'60'b_1066 v2
du_p'60'b_1066 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_1066 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_1068 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_s'60'b_1068 v2
du_s'60'b_1068 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1068 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1070 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1070 v2
du_cl'60'b_1070 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1070 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1072 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1072 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1072 v2
du_k'60'b_1072 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1072 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1074 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_1074 v2
du_setup_1074 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1074 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_152 (coe du_k'60'b_1072 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe du_cl'60'b_1070 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe du_k'60'b_1072 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1082 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_1082 v2
du_call_1082 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1082 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_152 (coe du_k'60'b_1072 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe du_cl'60'b_1070 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_152 (coe du_k'60'b_1072 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_1090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_1090 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_1090 v2
du_I'8321'_1090 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_1090 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_118)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_118)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_152
                                                               (coe du_p'60'b_1066 (coe v0)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_118)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_152
                                                                     (coe du_s'60'b_1068 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_118)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_118)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_118)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'slot_152
                                                                                 (coe
                                                                                    du_p'60'b_1066
                                                                                    (coe v0))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_118)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       du_sb'45'slot_152
                                                                                       (coe
                                                                                          du_s'60'b_1068
                                                                                          (coe v0))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          du_sb'45'none_118)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_1100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_1100 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_1100 v2
du_I'8322'_1100 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_1100 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_152 (coe du_p'60'b_1066 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_152 (coe du_s'60'b_1068 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_152 (coe du_p'60'b_1066 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_118)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152 (coe du_s'60'b_1068 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_1110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_1110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_1110
du_I'8323'_1110 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_1110
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.cata-linear-below
d_cata'45'linear'45'below_1120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'linear'45'below_1120 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_656
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
               (coe addInt (coe (7 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (7 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      (coe
         du_segok'45'idle_618
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                  (coe addInt (coe (7 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe addInt (coe (6 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (4 :: Integer)) (coe v3))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe addInt (coe (7 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
         (coe du_setup_1154 (coe v2)))
      (coe
         du_segok'45''43''43'_656
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                (coe addInt (coe (2 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v3))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252
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
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
         (coe
            du_segok'45'idle_618
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                              (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                   (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                               (coe
                                                                  addInt (coe (5 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (2 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v3))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252
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
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
            (coe du_I'8321'_1170 (coe v2)))
         (coe
            du_segok'45''43''43'_656
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                        (coe addInt (coe (6 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (7 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
            (coe
               du_segok'45'idle_618
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                           (coe addInt (coe (6 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                    (coe addInt (coe (7 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
               (coe du_call_1162 (coe v2)))
            (coe
               du_segok'45''43''43'_656
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                           (coe addInt (coe (4 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                       (coe addInt (coe (5 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                   (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                         (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                                     (coe (2 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                                              (coe (1 :: Integer)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v2)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
               (coe
                  du_segok'45'idle_618
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (3 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                              (coe addInt (coe (4 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                                           (coe v2))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                                                                                 (coe
                                                                                    (1 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v2)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                                             (coe
                                                                                                v2))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
                  (coe du_I'8322'_1190 (coe v2)))
               (coe
                  du_segok'45''43''43'_656
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                           (coe addInt (coe (7 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                              (coe addInt (coe (6 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (7 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                  (coe
                     du_segok'45'idle_618
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe addInt (coe (7 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                     (coe du_call_1162 (coe v2)))
                  (coe
                     du_segok'45''43''43'_656
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        du_segok'45'idle_618
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_1212))
                     (coe
                        du_cata'45'body'45'below_986 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_78
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (5 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> Integer
d_b_1136 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_1136 v2
du_b_1136 :: Integer -> Integer
du_b_1136 v0 = coe addInt (coe (8 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_1138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_1138 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p0_1138 v2
du_p0_1138 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_1138 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_1140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_1140 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p1_1140 v2
du_p1_1140 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_1140 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_1142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_1142 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p2_1142 v2
du_p2_1142 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_1142 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_1144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_1144 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p3_1144 v2
du_p3_1144 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_1144 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_1146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_1146 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p4_1146 v2
du_p4_1146 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_1146 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_1148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_1148 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p5_1148 v2
du_p5_1148 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_1148 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1150 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1150 v2
du_cl'60'b_1150 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1150 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (7 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1152 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1152 v2
du_k'60'b_1152 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1152 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (8 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1154 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_1154 v2
du_setup_1154 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1154 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_152 (coe du_k'60'b_1152 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe du_cl'60'b_1150 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe du_k'60'b_1152 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1162 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_1162 v2
du_call_1162 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1162 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_152 (coe du_k'60'b_1152 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe du_cl'60'b_1150 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_152 (coe du_k'60'b_1152 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_1170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_1170 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_1170 v2
du_I'8321'_1170 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_1170 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe du_p3_1144 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe du_p5_1148 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_152 (coe du_p2_1142 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_152 (coe du_p1_1140 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_152 (coe du_p5_1148 (coe v0))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_152
                                                            (coe du_p3_1144 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_118)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  du_sb'45'slot_152
                                                                  (coe du_p1_1140 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_152
                                                                     (coe du_p3_1144 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_152
                                                                        (coe du_p2_1142 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_118)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_118)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_118)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_118)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_1190 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_1190 v2
du_I'8322'_1190 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_1190 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe du_p4_1146 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe du_p3_1144 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_152 (coe du_p5_1148 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_152 (coe du_p3_1144 (coe v0)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_152 (coe du_p1_1140 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_118)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'slot_152 (coe du_p5_1148 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_152 (coe du_p4_1146 (coe v0))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_152
                                                            (coe du_p0_1138 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_118)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_118)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_118)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_152
                                                                        (coe du_p1_1140 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_118)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              du_sb'45'slot_152
                                                                              (coe
                                                                                 du_p0_1138
                                                                                 (coe v0))
                                                                              erased)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_118)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_1212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_1212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_1212
du_I'8323'_1212 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_1212
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.push2-below
d_push2'45'below_1222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_1222 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_push2'45'below_1222 v5 v6 v7
du_push2'45'below_1222 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_1222 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_152 (coe v1) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe v2) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_152 (coe v1) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_152 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_152 (coe v2) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe v0) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.pop2-below
d_pop2'45'below_1254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_1254 ~v0 ~v1 ~v2 v3 = du_pop2'45'below_1254 v3
du_pop2'45'below_1254 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_1254 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_152 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe v0) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.SlotBudget.wrap-sum-below
d_wrap'45'sum'45'below_1272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_1272 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_wrap'45'sum'45'below_1272 v4 v5
du_wrap'45'sum'45'below_1272 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_1272 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_152 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe v1) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_152 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_152 (coe v1) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
-- Once.CCC.Codegen.SlotBudget.visit-below
d_visit'45'below_1306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_visit'45'below_1306 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_visit'45'below_1306 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_visit'45'below_1306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
du_visit'45'below_1306 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_114 v11
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_118)
             (coe du_push2'45'below_1222 (coe v7) (coe v8) (coe v9))
      MAlonzo.Code.Once.Type.C__'8853'__118 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_118)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_118)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v11)))
                      (coe v6)))
                (coe
                   du_visit'45'below_1306 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v11)))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1380 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_118)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_118)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_118)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                         (coe v0) (coe v2) (coe v3) (coe v4) (coe v11)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         du_visit'45'below_1306 (coe v0) (coe v11) (coe v2) (coe v3)
                         (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v7) (coe v8)
                         (coe v9) (coe du_recF_1376 (coe v11) (coe v12) (coe v5) (coe v10)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_152
                      (coe du_s'60'b_1416 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_118)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v11))
                      (coe v6)))
                (coe
                   du_visit'45'below_1306 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v11))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1424 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2232
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_152
                         (coe du_s'60'b_1416 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_118)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_1306 (coe v0) (coe v11) (coe v2) (coe v3)
                      (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe du_recF_1420 (coe v11) (coe v12) (coe v5) (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_recF_1376 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1376 v1 v2 v6 v12
du_recF_1376 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1376 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_recG_1380 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1380 v1 v2 v6 v12
du_recG_1380 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1380 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_room4_1412 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_room4_1412 v1 v2 v6 v12
du_room4_1412 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1412 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_s'60'b_1416 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_s'60'b_1416 v1 v2 v6 v12
du_s'60'b_1416 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1416 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1412 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_recF_1420 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1420 v1 v2 v6 v12
du_recF_1420 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1420 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
d_recG_1424 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1424 v1 v2 v6 v12
du_recG_1424 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1424 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.rebuild-below
d_rebuild'45'below_1446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'below_1446 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_rebuild'45'below_1446 v0 v1 v2 v5 v6 v8 v9
du_rebuild'45'below_1446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_1446 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_114 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_118)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe du_pop2'45'below_1254 (coe v5)
      MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_118)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_118)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                   (coe v0) (coe v2) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7)))
                      (coe v4)))
                (coe
                   du_rebuild'45'below_1446 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7)))
                      (coe v4))
                   (coe v5) (coe du_recG_1520 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
                      (coe (1 :: Integer)) (coe v3))
                   (coe
                      du_wrap'45'sum'45'below_1272
                      (coe du_s'60'b_1508 (coe v7) (coe v8) (coe v3) (coe v6))
                      (coe du_b'45'ss_1512 (coe v7) (coe v8) (coe v3) (coe v6)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_118)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_118)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_118)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                            (coe v0) (coe v2) (coe v7)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            du_rebuild'45'below_1446 (coe v0) (coe v7) (coe v2)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5)
                            (coe du_recF_1516 (coe v7) (coe v8) (coe v3) (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
                               (coe (0 :: Integer)) (coe v3))
                            (coe
                               du_wrap'45'sum'45'below_1272
                               (coe du_s'60'b_1508 (coe v7) (coe v8) (coe v3) (coe v6))
                               (coe du_b'45'ss_1512 (coe v7) (coe v8) (coe v3) (coe v6)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_118)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_152
                      (coe du_s'60'b_1552 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_118)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_118)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                   (coe v0) (coe v2) (coe v7)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                (coe
                   du_rebuild'45'below_1446 (coe v0) (coe v7) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe du_recF_1572 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2232
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_152
                         (coe du_b'45'ss_1556 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_152
                            (coe du_s'60'b_1552 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_118)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_118)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                         (coe v0) (coe v2) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7))
                            (coe v4)))
                      (coe
                         du_rebuild'45'below_1446 (coe v0) (coe v8) (coe v2)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7))
                            (coe v4))
                         (coe v5) (coe du_recG_1576 (coe v7) (coe v8) (coe v3) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_152
                            (coe du_b'45's2_1560 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_118)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  du_sb'45'slot_152
                                  (coe du_b'45's3_1566 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_118)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        du_sb'45'slot_152
                                        (coe du_b'45'ss_1556 (coe v7) (coe v8) (coe v3) (coe v6))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe du_sb'45'none_118)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              du_sb'45'slot_152
                                              (coe
                                                 du_b'45's2_1560 (coe v7) (coe v8) (coe v3)
                                                 (coe v6))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe du_sb'45'none_118)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe
                                                    du_sb'45'slot_152
                                                    (coe
                                                       du_b'45's3_1566 (coe v7) (coe v8) (coe v3)
                                                       (coe v6))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_1504 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1504 v1 v2 v6 v10
du_room4_1504 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1504 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_1508 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1508 v1 v2 v6 v10
du_s'60'b_1508 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1508 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1504 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45'ss_1512 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1512 v1 v2 v6 v10
du_b'45'ss_1512 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1512 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1504 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_1516 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1516 v1 v2 v6 v10
du_recF_1516 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1516 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_1520 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1520 v1 v2 v6 v10
du_recG_1520 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1520 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_1548 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1548 v1 v2 v6 v10
du_room4_1548 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1548 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_1552 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1552 v1 v2 v6 v10
du_s'60'b_1552 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1552 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1548 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45'ss_1556 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1556 v1 v2 v6 v10
du_b'45'ss_1556 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1556 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1548 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_1560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45's2_1560 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's2_1560 v1 v2 v6 v10
du_b'45's2_1560 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_1560 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_1548 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_1566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'45's3_1566 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's3_1566 v1 v2 v6 v10
du_b'45's3_1566 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_1566 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_1548 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recF_1572 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1572 v1 v2 v6 v10
du_recF_1572 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1572 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_recG_1576 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1576 v1 v2 v6 v10
du_recG_1576 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1576 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.visit-idle
d_visit'45'idle_1608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_1608 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1670 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'branching'45'below_1730 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_segok'45''43''43'_656
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
               (coe
                  addInt
                  (coe
                     addInt (coe (12 :: Integer))
                     (coe
                        mulInt (coe (4 :: Integer))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                  (coe v3)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe
                        addInt
                        (coe
                           addInt (coe (11 :: Integer))
                           (coe
                              mulInt (coe (4 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe
                                       addInt
                                       (coe
                                          addInt
                                          (coe
                                             addInt (coe (4 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                                (coe v1)))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                             (coe v1)))
                                       (coe v4))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe
                                          addInt
                                          (coe
                                             addInt (coe (12 :: Integer))
                                             (coe
                                                mulInt (coe (4 :: Integer))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
                                                   (coe v1))))
                                          (coe v3)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      (coe
         du_segok'45'idle_618
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                  (coe
                     addInt
                     (coe
                        addInt (coe (12 :: Integer))
                        (coe
                           mulInt (coe (4 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                     (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe
                           addInt
                           (coe
                              addInt (coe (11 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe
                                          addInt
                                          (coe
                                             addInt
                                             (coe
                                                addInt (coe (4 :: Integer))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                                   (coe v1)))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                                (coe v1)))
                                          (coe v4))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                          (coe
                                             addInt
                                             (coe
                                                addInt (coe (12 :: Integer))
                                                (coe
                                                   mulInt (coe (4 :: Integer))
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
                                                      (coe v1))))
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
         (coe du_setup_1758 (coe v1) (coe v3)))
      (coe
         du_segok'45''43''43'_656
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_320
            (coe v0) (coe v1) (coe v3) (coe v4))
         (coe
            du_segok'45'weaken_684 (coe du_b_1748 (coe v1) (coe v3))
            (coe
               du_cata'45'budget'45'of_78
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
                  (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28
                     (coe v1))
                  (coe v2) (coe v3) (coe v4) (coe v5)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_320
               (coe v0) (coe v1) (coe v3) (coe v4))
            (coe du_b'8804'b2_1750 (coe v1) (coe v3))
            (coe
               du_segok'45'idle_618
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_320
                  (coe v0) (coe v1) (coe v3) (coe v4))
               (coe du_I'8321''45'all_1808 (coe v0) (coe v1) (coe v3) (coe v4))))
         (coe
            du_segok'45''43''43'_656
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe
                        addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe
                              mulInt (coe (4 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                        (coe
                           addInt
                           (coe
                              addInt (coe (11 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (12 :: Integer))
                                       (coe
                                          mulInt (coe (4 :: Integer))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
                                             (coe v1))))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
            (coe
               du_segok'45'idle_618
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                        (coe
                           addInt
                           (coe
                              addInt (coe (12 :: Integer))
                              (coe
                                 mulInt (coe (4 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v1))))
                           (coe v3)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                           (coe
                              addInt
                              (coe
                                 addInt (coe (11 :: Integer))
                                 (coe
                                    mulInt (coe (4 :: Integer))
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
                                       (coe v1))))
                              (coe v3)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                    (coe
                                       addInt
                                       (coe
                                          addInt (coe (12 :: Integer))
                                          (coe
                                             mulInt (coe (4 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150
                                                (coe v1))))
                                       (coe v3)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
               (coe du_call_1766 (coe v1) (coe v3)))
            (coe
               du_segok'45''43''43'_656
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_328
                  (coe v0) (coe v3) (coe v4))
               (coe
                  du_segok'45'weaken_684 (coe du_b_1748 (coe v1) (coe v3))
                  (coe
                     du_cata'45'budget'45'of_78
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28
                           (coe v1))
                        (coe v2) (coe v3) (coe v4) (coe v5)))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_328
                     (coe v0) (coe v3) (coe v4))
                  (coe du_b'8804'b2_1750 (coe v1) (coe v3))
                  (coe
                     du_segok'45'idle_618
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_328
                        (coe v0) (coe v3) (coe v4))
                     (coe du_I'8322''45'all_1842 (coe v1) (coe v3))))
               (coe
                  du_cata'45'body'45'below_986 (coe v0)
                  (coe
                     du_cata'45'budget'45'of_78
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
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
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v1)))
                     (coe v4))
                  (coe v5) (coe v6)))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> Integer
d_b_1748 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_b_1748 v1 v3
du_b_1748 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> Integer -> Integer
du_b_1748 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.SlotBudget._.b≤b2
d_b'8804'b2_1750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'8804'b2_1750 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_b'8804'b2_1750 v1 v3
du_b'8804'b2_1750 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'8804'b2_1750 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe du_b_1748 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.b+2
d_b'43'2_1752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'43'2_1752 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_b'43'2_1752 v1 v3
du_b'43'2_1752 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'43'2_1752 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe addInt (coe (2 :: Integer)) (coe du_b_1748 (coe v0) (coe v1)))
-- Once.CCC.Codegen.SlotBudget._.cl<b2
d_cl'60'b2_1754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b2_1754 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_cl'60'b2_1754 v1 v3
du_cl'60'b2_1754 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b2_1754 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_b_1748 (coe v0) (coe v1))))
      (coe du_b'43'2_1752 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.k<b2
d_k'60'b2_1756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b2_1756 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_k'60'b2_1756 v1 v3
du_k'60'b2_1756 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b2_1756 v0 v1 = coe du_b'43'2_1752 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1758 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_setup_1758 v1 v3
du_setup_1758 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1758 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            du_sb'45'slot_152 (coe du_k'60'b2_1756 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  du_sb'45'slot_152 (coe du_cl'60'b2_1754 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152 (coe du_k'60'b2_1756 (coe v0) (coe v1))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1766 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_call_1766 v1 v3
du_call_1766 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1766 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_118)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            du_sb'45'slot_152 (coe du_k'60'b2_1756 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               du_sb'45'slot_152 (coe du_cl'60'b2_1754 (coe v0) (coe v1)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        du_sb'45'slot_152 (coe du_k'60'b2_1756 (coe v0) (coe v1)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1774 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7_1774 v1 v3
du_fixed7_1774 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1774 v0 v1
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
            (coe v1)))
-- Once.CCC.Codegen.SlotBudget._.fixed7'
d_fixed7''_1776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1776 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7''_1776 v1 v3
du_fixed7''_1776 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1776 v0 v1 = coe du_fixed7_1774 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1780 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q0_1780 v1 v3
du_q0_1780 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1780 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1782 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q1_1782 v1 v3
du_q1_1782 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1782 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1784 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q2_1784 v1 v3
du_q2_1784 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1784 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1788 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q3_1788 v1 v3
du_q3_1788 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1788 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1792 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q4_1792 v1 v3
du_q4_1792 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1792 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1796 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q5_1796 v1 v3
du_q5_1796 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1796 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1800 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q6_1800 v1 v3
du_q6_1800 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1800 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1776 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1804 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_walk'45'room_1804 v1 v3
du_walk'45'room_1804 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1804 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe
         addInt
         (coe
            addInt (coe (7 :: Integer))
            (coe
               mulInt (coe (4 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
         (coe v1))
-- Once.CCC.Codegen.SlotBudget._.I₁-idle
d_I'8321''45'idle_1806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1806 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1808 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_I'8321''45'all_1808 v0 v1 v3 v4
du_I'8321''45'all_1808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1808 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_152 (coe du_q3_1788 (coe v1) (coe v2)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_152 (coe du_q6_1800 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_152 (coe du_q6_1800 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe du_q1_1782 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_152 (coe du_q6_1800 (coe v1) (coe v2)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152 (coe du_q2_1784 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152 (coe du_q6_1800 (coe v1) (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_152 (coe du_q0_1780 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_152
                                                   (coe du_q3_1788 (coe v1) (coe v2)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            du_push2'45'below_1222 (coe du_q0_1780 (coe v1) (coe v2))
            (coe du_q4_1792 (coe v1) (coe v2))
            (coe du_q5_1796 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_118)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_152 (coe du_q0_1780 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_152 (coe du_q0_1780 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152 (coe du_q3_1788 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152 (coe du_q3_1788 (coe v1) (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  du_push2'45'below_1222 (coe du_q1_1782 (coe v1) (coe v2))
                  (coe du_q4_1792 (coe v1) (coe v2))
                  (coe du_q5_1796 (coe v1) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_152 (coe du_q3_1788 (coe v1) (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_118)
                        (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                        (coe v0) (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        du_visit'45'below_1306 (coe v0) (coe v1) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3))
                        (coe du_q0_1780 (coe v1) (coe v2))
                        (coe du_q4_1792 (coe v1) (coe v2))
                        (coe du_q5_1796 (coe v1) (coe v2))
                        (coe du_walk'45'room_1804 (coe v1) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_118)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_152 (coe du_q1_1782 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_118)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_152 (coe du_q1_1782 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                                 (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                          (coe v1)))
                                    (coe v3)))
                              (coe
                                 du_rebuild'45'below_1446 (coe v0) (coe v1)
                                 (coe addInt (coe (2 :: Integer)) (coe v2))
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                          (coe v1)))
                                    (coe v3))
                                 (coe du_q2_1784 (coe v1) (coe v2))
                                 (coe du_walk'45'room_1804 (coe v1) (coe v2)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_118)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1842 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_I'8322''45'all_1842 v1 v3
du_I'8322''45'all_1842 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1842 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_1222 (coe du_q2_1784 (coe v0) (coe v1))
         (coe du_q4_1792 (coe v0) (coe v1))
         (coe du_q5_1796 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_118)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_118)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_152 (coe du_q2_1784 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_118)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_118)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_SegOK_590 -> T_SegOK_590
d_cata'45'slots'45'below_1856 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             d_cata'45'const'45'below_1006 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             d_cata'45'nat'45'below_1048 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             d_cata'45'linear'45'below_1120 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             d_cata'45'branching'45'below_1730 (coe v0) (coe v7) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_1910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer -> T_SegOK_590
d_slots'45'below_1910 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v1) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             du_segok'45''43''43'_656
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                du_segok'45'weaken_684
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_budget'45'of_70
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10)))
                (coe
                   du_trace'45'of_74
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   d_frontier'45'mono_804 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
                (coe
                   d_slots'45'below_1910 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                   (coe v5)))
             (coe
                du_segok'45'pre_696
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_118)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_1910 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_696
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe v4))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          d_h_1952 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                          (coe v10) (coe v4) (coe v5)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_656
                              (coe
                                 du_trace'45'of_74
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_segok'45'weaken_684
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    du_budget'45'of_70
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
                                          v11)))
                                 (coe
                                    du_trace'45'of_74
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    d_frontier'45'mono_804 (coe v0) (coe v1) (coe v13) (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))))
                                 (coe
                                    d_slots'45'below_1910 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)))
                              (coe
                                 du_segok'45'pre_696
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2232
                                          (coe v4))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_152
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             d_h_1952 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                             (coe v10) (coe v4) (coe v5)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                d_h_1952 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_656
                                    (coe
                                       du_trace'45'of_74
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v13)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                   (coe v0) (coe v1) (coe v12)
                                                   (coe addInt (coe (3 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9))))
                                          (coe v10)))
                                    (coe
                                       d_slots'45'below_1910 (coe v0) (coe v1) (coe v13) (coe v10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))))
                                    (coe
                                       du_segok'45'idle_618
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2230
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152
                                             (coe
                                                d_h_1952 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_152
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   (coe
                                                      d_h_1952 (coe v0) (coe v1) (coe v12) (coe v13)
                                                      (coe v9) (coe v10) (coe v4) (coe v5)))
                                                (coe
                                                   (\ v14 v15 ->
                                                      d_h_1952
                                                        (coe v0) (coe v1) (coe v12) (coe v13)
                                                        (coe v9) (coe v10) (coe v4) (coe v5))))
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_696
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe v4))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          d_h_1976 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                          (coe v10) (coe v4) (coe v5)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_656
                              (coe
                                 du_trace'45'of_74
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_segok'45'weaken_684
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    du_budget'45'of_70
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
                                          v11)))
                                 (coe
                                    du_trace'45'of_74
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    d_frontier'45'mono_804 (coe v0) (coe v1) (coe v13) (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))))
                                 (coe
                                    d_slots'45'below_1910 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)))
                              (coe
                                 du_segok'45'pre_696
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2232
                                          (coe v4))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_152
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             d_h_1976 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                             (coe v10) (coe v4) (coe v5)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                d_h_1976 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_656
                                    (coe
                                       du_trace'45'of_74
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v1) (coe v13)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                   (coe v0) (coe v1) (coe v12)
                                                   (coe addInt (coe (4 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9))))
                                          (coe v10)))
                                    (coe
                                       d_slots'45'below_1910 (coe v0) (coe v1) (coe v13) (coe v10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))))
                                    (coe
                                       du_segok'45'idle_618
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                                   (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v4)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                (coe
                                                   d_h_1976 (coe v0) (coe v1) (coe v12) (coe v13)
                                                   (coe v9) (coe v10) (coe v4) (coe v5)))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_152
                                                   (coe
                                                      d_h_1976 (coe v0) (coe v1) (coe v12) (coe v13)
                                                      (coe v9) (coe v10) (coe v4) (coe v5))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_152
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            (coe
                                                               d_h_1976 (coe v0) (coe v1) (coe v12)
                                                               (coe v13) (coe v9) (coe v10) (coe v4)
                                                               (coe v5)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_118)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_152
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                  (coe
                                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v4)))
                                                                  (coe
                                                                     d_h_1976 (coe v0) (coe v1)
                                                                     (coe v12) (coe v13) (coe v9)
                                                                     (coe v10) (coe v4) (coe v5)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_118)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_152
                                                                     (coe
                                                                        d_h_1976 (coe v0) (coe v1)
                                                                        (coe v12) (coe v13) (coe v9)
                                                                        (coe v10) (coe v4) (coe v5))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v9))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_fst_44)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_snd_50)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_618
                           (coe
                              du_trace'45'of_74
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                (\ v11 v12 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v11)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'idle_618
                           (coe
                              du_trace'45'of_74
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_152
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_152
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_618
                           (coe
                              du_trace'45'of_74
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                (\ v11 v12 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v11)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'idle_618
                           (coe
                              du_trace'45'of_74
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_152
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_152
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    du_segok'45'pre_696
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe du_sb'45'none_118)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_118)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       du_segok'45''43''43'_656
                       (coe
                          du_trace'45'of_74
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                             (coe v0) (coe v12) (coe v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                             (coe v10)))
                       (coe
                          d_slots'45'below_1910 (coe v0) (coe v12) (coe v2) (coe v10)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                       (coe
                          du_segok'45'pre_696
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_118)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe du_sb'45'none_118)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_118)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe du_sb'45'none_118)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                          (coe
                             du_segok'45''43''43'_656
                             (coe
                                du_trace'45'of_74
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                du_segok'45'weaken_684
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   du_budget'45'of_70
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                      (coe MAlonzo.Code.Once.IR.C_case_70 v9 v10)))
                                (coe
                                   du_trace'45'of_74
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   d_frontier'45'mono_804 (coe v0) (coe v12) (coe v2) (coe v10)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                         (coe v0) (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                            (coe v0) (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                                (coe
                                   d_slots'45'below_1910 (coe v0) (coe v11) (coe v2) (coe v9)
                                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5))))
                             (coe
                                du_segok'45'idle_618
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_118)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_terminal_74)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v2) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_initial_78)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_696
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2230
                                             (coe v4))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_152
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                (\ v13 v14 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v13)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                           (coe
                              du_segok'45'thunk_716
                              (coe
                                 du_budget'45'of_70
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                          (coe v12) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                              (coe
                                 d_slots'45'below_1910 (coe v0)
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                 (coe v12) (coe v9) (coe (0 :: Integer))
                                 (coe addInt (coe (2 :: Integer)) (coe v5))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_696
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                (coe v4))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0) (coe v5)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v4)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                     (coe v0)
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v5)))))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_152
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_152
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_118)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_118)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_152
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_118)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
                           (coe
                              du_segok'45'thunk_716
                              (coe
                                 du_budget'45'of_70
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                          (coe v12) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                              (coe
                                 d_slots'45'below_1910 (coe v0)
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                 (coe v12) (coe v9) (coe (0 :: Integer))
                                 (coe addInt (coe (2 :: Integer)) (coe v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                      -> coe
                           du_segok'45'idle_618
                           (coe
                              du_trace'45'of_74
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v10) (coe v2))
                                    (coe v10))
                                 (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_118)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_152
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_118)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_118)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_118)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_118)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_152
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_118)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_152
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v4)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_118)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_152
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v4)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_118)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_152
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v4)))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_118)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_152
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
                                                                           (coe du_sb'45'none_118)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_118)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    d_cata'45'slots'45'below_1856 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                          (coe v2) (coe (0 :: Integer)) (coe v5) (coe v9)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                             (coe v2) (coe (0 :: Integer)) (coe v5) (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                                (coe v2) (coe (0 :: Integer)) (coe v5) (coe v9)))))
                    (coe
                       d_slots'45'below_1910 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                       (coe v2) (coe v9) (coe (0 :: Integer)) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v7 v9
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Para_112 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Out_116 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_Out_116 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8)))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_126 v7 v9
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_126 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v6
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4) (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_const_148 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    du_segok'45'idle_618
                    (coe
                       du_trace'45'of_74
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_118)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
        -> coe
             du_segok'45'idle_618
             (coe
                du_trace'45'of_74
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7)) (coe v4)
                   (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_118)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1952 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_804 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_804 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_70
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1976 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_804 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_804 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_70
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget.trace-lookup
d_trace'45'lookup_2144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
d_trace'45'lookup_2144 ~v0 v1 v2 = du_trace'45'lookup_2144 v1 v2
du_trace'45'lookup_2144 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
du_trace'45'lookup_2144 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_trace'45'lookup_2144 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.fetch-at
d_fetch'45'at_2152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
d_fetch'45'at_2152 ~v0 = du_fetch'45'at_2152
du_fetch'45'at_2152 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
du_fetch'45'at_2152 = coe du_trace'45'lookup_2144
-- Once.CCC.Codegen.SlotBudget.seg-at
d_seg'45'at_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> T_SegState_222 -> T_SegState_222
d_seg'45'at_2154 ~v0 v1 v2 v3 = du_seg'45'at_2154 v1 v2 v3
du_seg'45'at_2154 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> T_SegState_222 -> T_SegState_222
du_seg'45'at_2154 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       du_seg'45'at_2154 (coe v5) (coe v3)
                       (coe du_seg'45'step_264 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotBudget.seg-at-suc
d_seg'45'at'45'suc_2176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_SegState_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_2176 = erased
-- Once.CCC.Codegen.SlotBudget.idle-seg-at
d_idle'45'seg'45'at_2204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_2204 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_2238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  T_SegState_222 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_2238 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_2274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  T_SegState_222 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_2274 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ˡ
d_fetch'45''43''43''737'_2298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_2298 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ʳ
d_fetch'45''43''43''691'_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_2326 = erased
-- Once.CCC.Codegen.SlotBudget.split-pos
d_split'45'pos_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_2346 ~v0 v1 v2 = du_split'45'pos_2346 v1 v2
du_split'45'pos_2346 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split'45'pos_2346 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
      (:) v2 v3
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (let v5 = coe du_split'45'pos_2346 (coe v3) (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                            -> coe
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                 (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           erased)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.allseg-at
d_allseg'45'at_2390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_222 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_AllSeg_300 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_90
d_allseg'45'at_2390 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_allseg'45'at_2390 v2 v3 v5
du_allseg'45'at_2390 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer -> T_AllSeg_300 -> T_SlotBelow_90
du_allseg'45'at_2390 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__312 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__312 v9 v10
                         -> coe du_allseg'45'at_2390 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-seg
d_ir'45'slots'45'below'45'seg_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_SegOK_590
d_ir'45'slots'45'below'45'seg_2420 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
              (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
              (coe (0 :: Integer)) (coe v3) in
    coe
      (let v5
             = d_slots'45'below_1910
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer))
                 (coe (0 :: Integer)) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
              -> case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> coe seq (coe v9) (coe v5)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Codegen.SlotBudget.emitted-slot-seg
d_emitted'45'slot'45'seg_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_2444 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_emitted'45'slot'45'seg_2444 v0 v1 v2 v3 v4 v6
du_emitted'45'slot'45'seg_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_2444 v0 v1 v2 v3 v4 v5
  = coe
      d_below_106
      (coe
         du_allseg'45'at_2390
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_732
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4)
         (coe
            d_ok'45'all_606
            (d_ir'45'slots'45'below'45'seg_2420
               (coe v0) (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      v5 erased
