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
import qualified MAlonzo.Code.Data.List.Base
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'br'45'I'8321'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₂
d_cata'45'br'45'I'8322'_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
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
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_742
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace
d_ir'45'to'45'trace_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
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
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.pop2
d_pop2_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_pop2_44 ~v0 = du_pop2_44
du_pop2_44 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_pop2_44
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_182
-- Once.CCC.Codegen.SlotBudget._.push2
d_push2_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_push2_46 ~v0 = du_push2_46
du_push2_46 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_push2_46
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
-- Once.CCC.Codegen.SlotBudget._.rebuild-walk
d_rebuild'45'walk_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_rebuild'45'walk_48 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.SlotBudget._.visit-walk
d_visit'45'walk_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_visit'45'walk_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.wrap-sum
d_wrap'45'sum_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_wrap'45'sum_60 ~v0 = du_wrap'45'sum_60
du_wrap'45'sum_60 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_wrap'45'sum_60
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_72 ~v0 v1 = du_budget'45'of_72 v1
du_budget'45'of_72 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_72 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace'45'of_76 ~v0 v1 = du_trace'45'of_76 v1
du_trace'45'of_76 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_trace'45'of_76 v0
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
d_cata'45'budget'45'of_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_80 ~v0 v1 = du_cata'45'budget'45'of_80 v1
du_cata'45'budget'45'of_80 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'budget'45'of_80 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'trace'45'of_84 ~v0 v1 = du_cata'45'trace'45'of_84 v1
du_cata'45'trace'45'of_84 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_cata'45'trace'45'of_84 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow
d_SlotBelow_92 a0 a1 a2 = ()
data T_SlotBelow_92
  = C_mkSlotBelow_114 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.SlotBudget.SlotBelow.below
d_below_108 ::
  T_SlotBelow_92 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_108 v0
  = case coe v0 of
      C_mkSlotBelow_114 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow.pair-below
d_pair'45'below_112 ::
  T_SlotBelow_92 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pair'45'below_112 v0
  = case coe v0 of
      C_mkSlotBelow_114 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-none
d_sb'45'none_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_92
d_sb'45'none_120 ~v0 ~v1 ~v2 ~v3 = du_sb'45'none_120
du_sb'45'none_120 :: T_SlotBelow_92
du_sb'45'none_120
  = coe
      C_mkSlotBelow_114 (coe (\ v0 v1 -> coe du_go_136))
      (coe (\ v0 v1 -> coe du_go_136))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_go_136
du_go_136 :: AgdaAny
du_go_136 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-slot
d_sb'45'slot_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_92
d_sb'45'slot_154 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_sb'45'slot_154 v5 v6
du_sb'45'slot_154 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_92
du_sb'45'slot_154 v0 v1
  = coe C_mkSlotBelow_114 (coe (\ v2 v3 -> v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.just-inj
d_just'45'inj_172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_172 = erased
-- Once.CCC.Codegen.SlotBudget.sb-weaken
d_sb'45'weaken_186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_186 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sb'45'weaken_186 v3 v4 v5
du_sb'45'weaken_186 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sb'45'weaken_186 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       C_mkSlotBelow_114
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_below_108 v5 v9 erased) (coe v1)))
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_pair'45'below_112 v5 v9 erased) (coe v1))))
                    (coe du_sb'45'weaken_186 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-le
d_sb'45'le_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_92 -> T_SlotBelow_92
d_sb'45'le_210 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sb'45'le_210 v4 v5
du_sb'45'le_210 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_92 -> T_SlotBelow_92
du_sb'45'le_210 v0 v1
  = coe
      C_mkSlotBelow_114
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_below_108 v1 v2 erased) (coe v0)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_pair'45'below_112 v1 v2 erased) (coe v0)))
-- Once.CCC.Codegen.SlotBudget.SegState
d_SegState_224 a0 = ()
data T_SegState_224 = C_mkSeg_234 Integer [Integer]
-- Once.CCC.Codegen.SlotBudget.SegState.cur
d_cur_230 :: T_SegState_224 -> Integer
d_cur_230 v0
  = case coe v0 of
      C_mkSeg_234 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegState.saved
d_saved_232 :: T_SegState_224 -> [Integer]
d_saved_232 v0
  = case coe v0 of
      C_mkSeg_234 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegAction
d_SegAction_236 a0 = ()
data T_SegAction_236
  = C_seg'45'id_238 | C_seg'45'push_240 Integer | C_seg'45'pop_242
-- Once.CCC.Codegen.SlotBudget.seg-action
d_seg'45'action_244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_SegAction_236
d_seg'45'action_244 ~v0 v1 = du_seg'45'action_244 v1
du_seg'45'action_244 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_SegAction_236
du_seg'45'action_244 v0
  = let v1 = coe C_seg'45'id_238 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v3 v4
                  -> coe C_seg'45'push_240 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v3
                  -> coe C_seg'45'pop_242
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotBudget.pop-with
d_pop'45'with_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SegState_224 -> T_SegState_224
d_pop'45'with_248 ~v0 v1 v2 = du_pop'45'with_248 v1 v2
du_pop'45'with_248 :: [Integer] -> T_SegState_224 -> T_SegState_224
du_pop'45'with_248 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_234 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply
d_seg'45'apply_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_236 -> T_SegState_224 -> T_SegState_224
d_seg'45'apply_256 ~v0 v1 v2 = du_seg'45'apply_256 v1 v2
du_seg'45'apply_256 ::
  T_SegAction_236 -> T_SegState_224 -> T_SegState_224
du_seg'45'apply_256 v0 v1
  = case coe v0 of
      C_seg'45'id_238 -> coe v1
      C_seg'45'push_240 v2
        -> coe
             C_mkSeg_234 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_230 (coe v1)) (coe d_saved_232 (coe v1)))
      C_seg'45'pop_242
        -> coe du_pop'45'with_248 (coe d_saved_232 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-step
d_seg'45'step_266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_SegState_224 -> T_SegState_224
d_seg'45'step_266 ~v0 v1 v2 = du_seg'45'step_266 v1 v2
du_seg'45'step_266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_SegState_224 -> T_SegState_224
du_seg'45'step_266 v0 v1
  = coe
      du_seg'45'apply_256 (coe du_seg'45'action_244 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget.seg-fold
d_seg'45'fold_272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegState_224 -> T_SegState_224
d_seg'45'fold_272 ~v0 v1 v2 = du_seg'45'fold_272 v1 v2
du_seg'45'fold_272 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegState_224 -> T_SegState_224
du_seg'45'fold_272 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_seg'45'fold_272 (coe v3)
             (coe du_seg'45'step_266 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-fold-++
d_seg'45'fold'45''43''43'_288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_288 = erased
-- Once.CCC.Codegen.SlotBudget.AllSeg
d_AllSeg_302 a0 a1 a2 = ()
data T_AllSeg_302
  = C_'91''93'_306 | C__'8759'__314 T_SlotBelow_92 T_AllSeg_302
-- Once.CCC.Codegen.SlotBudget.allseg-++
d_allseg'45''43''43'_322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_224 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_AllSeg_302 -> T_AllSeg_302 -> T_AllSeg_302
d_allseg'45''43''43'_322 ~v0 ~v1 v2 ~v3 v4 v5
  = du_allseg'45''43''43'_322 v2 v4 v5
du_allseg'45''43''43'_322 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_AllSeg_302 -> T_AllSeg_302 -> T_AllSeg_302
du_allseg'45''43''43'_322 v0 v1 v2
  = case coe v1 of
      C_'91''93'_306 -> coe v2
      C__'8759'__314 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__314 v6
                    (coe du_allseg'45''43''43'_322 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.allseg-++bal
d_allseg'45''43''43'bal_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_224 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_302 -> T_AllSeg_302 -> T_AllSeg_302
d_allseg'45''43''43'bal_338 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_allseg'45''43''43'bal_338 v2 v5 v6
du_allseg'45''43''43'bal_338 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_AllSeg_302 -> T_AllSeg_302 -> T_AllSeg_302
du_allseg'45''43''43'bal_338 v0 v1 v2
  = coe du_allseg'45''43''43'_322 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotBudget.SavedLE
d_SavedLE_348 a0 a1 a2 = ()
data T_SavedLE_348
  = C_'91''93'_350 |
    C__'8759'__360 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_348
-- Once.CCC.Codegen.SlotBudget.SegLE
d_SegLE_366 a0 a1 a2 = ()
data T_SegLE_366
  = C_mkSegLE_380 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_348
-- Once.CCC.Codegen.SlotBudget.SegLE.cur-le
d_cur'45'le_376 ::
  T_SegLE_366 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_376 v0
  = case coe v0 of
      C_mkSegLE_380 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegLE.saved-le
d_saved'45'le_378 :: T_SegLE_366 -> T_SavedLE_348
d_saved'45'le_378 v0
  = case coe v0 of
      C_mkSegLE_380 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.saved-le-refl
d_saved'45'le'45'refl_384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SavedLE_348
d_saved'45'le'45'refl_384 ~v0 v1 = du_saved'45'le'45'refl_384 v1
du_saved'45'le'45'refl_384 :: [Integer] -> T_SavedLE_348
du_saved'45'le'45'refl_384 v0
  = case coe v0 of
      [] -> coe C_'91''93'_350
      (:) v1 v2
        -> coe
             C__'8759'__360
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (coe du_saved'45'le'45'refl_384 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.pop-mono
d_pop'45'mono_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_224 ->
  T_SegState_224 ->
  [Integer] ->
  [Integer] -> T_SavedLE_348 -> T_SegLE_366 -> T_SegLE_366
d_pop'45'mono_398 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pop'45'mono_398 v3 v4 v5 v6
du_pop'45'mono_398 ::
  [Integer] ->
  [Integer] -> T_SavedLE_348 -> T_SegLE_366 -> T_SegLE_366
du_pop'45'mono_398 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__360 v10 v11 -> coe C_mkSegLE_380 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply-mono
d_seg'45'apply'45'mono_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_236 ->
  T_SegState_224 -> T_SegState_224 -> T_SegLE_366 -> T_SegLE_366
d_seg'45'apply'45'mono_420 ~v0 v1 v2 v3 v4
  = du_seg'45'apply'45'mono_420 v1 v2 v3 v4
du_seg'45'apply'45'mono_420 ::
  T_SegAction_236 ->
  T_SegState_224 -> T_SegState_224 -> T_SegLE_366 -> T_SegLE_366
du_seg'45'apply'45'mono_420 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_238 -> coe v3
      C_seg'45'push_240 v4
        -> coe
             C_mkSegLE_380
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_230 (coe du_seg'45'apply_256 (coe v0) (coe v1))))
             (coe
                C__'8759'__360 (d_cur'45'le_376 (coe v3))
                (d_saved'45'le_378 (coe v3)))
      C_seg'45'pop_242
        -> coe
             du_pop'45'mono_398 (coe d_saved_232 (coe v1))
             (coe d_saved_232 (coe v2)) (coe d_saved'45'le_378 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken
d_seg'45'weaken_440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_224 ->
  T_SegState_224 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegLE_366 -> T_AllSeg_302 -> T_AllSeg_302
d_seg'45'weaken_440 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken_440 v1 v2 v3 v4 v5
du_seg'45'weaken_440 ::
  T_SegState_224 ->
  T_SegState_224 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegLE_366 -> T_AllSeg_302 -> T_AllSeg_302
du_seg'45'weaken_440 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_306 -> coe C_'91''93'_306
      C__'8759'__314 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__314
                    (coe du_sb'45'le_210 (coe d_cur'45'le_376 (coe v3)) (coe v8))
                    (coe
                       du_seg'45'weaken_440
                       (coe
                          du_seg'45'apply_256 (coe du_seg'45'action_244 (coe v10)) (coe v0))
                       (coe du_seg'45'step_266 (coe v10) (coe v1)) (coe v11)
                       (coe
                          du_seg'45'apply'45'mono_420 (coe du_seg'45'action_244 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken-cur
d_seg'45'weaken'45'cur_460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_302 -> T_AllSeg_302
d_seg'45'weaken'45'cur_460 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken'45'cur_460 v1 v2 v3 v4 v5
du_seg'45'weaken'45'cur_460 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_302 -> T_AllSeg_302
du_seg'45'weaken'45'cur_460 v0 v1 v2 v3 v4
  = coe
      du_seg'45'weaken_440 (coe C_mkSeg_234 (coe v0) (coe v2))
      (coe C_mkSeg_234 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_380 (coe v4) (coe du_saved'45'le'45'refl_384 (coe v2)))
-- Once.CCC.Codegen.SlotBudget.is-id?
d_is'45'id'63'_466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_236 -> Bool
d_is'45'id'63'_466 ~v0 v1 = du_is'45'id'63'_466 v1
du_is'45'id'63'_466 :: T_SegAction_236 -> Bool
du_is'45'id'63'_466 v0
  = case coe v0 of
      C_seg'45'id_238 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_240 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_242 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-idle?
d_seg'45'idle'63'_468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> Bool
d_seg'45'idle'63'_468 ~v0 v1 = du_seg'45'idle'63'_468 v1
du_seg'45'idle'63'_468 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> Bool
du_seg'45'idle'63'_468 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe du_is'45'id'63'_466 (coe du_seg'45'action_244 (coe v1)))
             (coe du_seg'45'idle'63'_468 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.idle-step
d_idle'45'step_478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_478 = erased
-- Once.CCC.Codegen.SlotBudget._.go
d_go_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_224 ->
  T_SegAction_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_492 = erased
-- Once.CCC.Codegen.SlotBudget.idle-head
d_idle'45'head_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_498 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-fst
d_'8743''45'fst_514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_514 = erased
-- Once.CCC.Codegen.SlotBudget.idle-tail
d_idle'45'tail_524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_524 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-snd
d_'8743''45'snd_540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_540 = erased
-- Once.CCC.Codegen.SlotBudget.idle-++
d_idle'45''43''43'_552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_552 = erased
-- Once.CCC.Codegen.SlotBudget.idle-neutral
d_idle'45'neutral_576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_576 = erased
-- Once.CCC.Codegen.SlotBudget.SegOK
d_SegOK_592 a0 a1 a2 = ()
newtype T_SegOK_592 = C_mkSegOK_614 ([Integer] -> T_AllSeg_302)
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-all
d_ok'45'all_608 :: T_SegOK_592 -> [Integer] -> T_AllSeg_302
d_ok'45'all_608 v0
  = case coe v0 of
      C_mkSegOK_614 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-neu
d_ok'45'neu_612 ::
  T_SegOK_592 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_612 = erased
-- Once.CCC.Codegen.SlotBudget.segok-idle
d_segok'45'idle_620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_592
d_segok'45'idle_620 ~v0 ~v1 v2 ~v3 v4 = du_segok'45'idle_620 v2 v4
du_segok'45'idle_620 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_592
du_segok'45'idle_620 v0 v1
  = coe C_mkSegOK_614 (\ v2 -> coe du_go_636 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_302
d_go_636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 = du_go_636 v6 v8
du_go_636 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_302
du_go_636 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_306)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__314 v6 (coe du_go_636 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.segok-++
d_segok'45''43''43'_658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592 -> T_SegOK_592
d_segok'45''43''43'_658 ~v0 ~v1 v2 ~v3 v4 v5
  = du_segok'45''43''43'_658 v2 v4 v5
du_segok'45''43''43'_658 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592 -> T_SegOK_592
du_segok'45''43''43'_658 v0 v1 v2
  = coe
      C_mkSegOK_614
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_338 (coe v0) (coe d_ok'45'all_608 v1 v3)
           (coe d_ok'45'all_608 v2 v3))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 ->
  T_SegOK_592 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_676 = erased
-- Once.CCC.Codegen.SlotBudget.segok-weaken
d_segok'45'weaken_686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_592 -> T_SegOK_592
d_segok'45'weaken_686 ~v0 v1 v2 v3 v4 v5
  = du_segok'45'weaken_686 v1 v2 v3 v4 v5
du_segok'45'weaken_686 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_592 -> T_SegOK_592
du_segok'45'weaken_686 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_614
      (\ v5 ->
         coe
           du_seg'45'weaken'45'cur_460 v0 v1 v5 v2 v3
           (coe d_ok'45'all_608 v4 v5))
-- Once.CCC.Codegen.SlotBudget.segok-pre
d_segok'45'pre_698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_592 -> T_SegOK_592
d_segok'45'pre_698 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_segok'45'pre_698 v2 v5 v6
du_segok'45'pre_698 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_592 -> T_SegOK_592
du_segok'45'pre_698 v0 v1 v2
  = coe
      du_segok'45''43''43'_658 (coe v0)
      (coe du_segok'45'idle_620 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotBudget.segok-thunk
d_segok'45'thunk_718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_segok'45'thunk_718 ~v0 v1 ~v2 ~v3 ~v4 v5 v6
  = du_segok'45'thunk_718 v1 v5 v6
du_segok'45'thunk_718 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
du_segok'45'thunk_718 v0 v1 v2
  = coe C_mkSegOK_614 (coe du_inner_738 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotBudget._.inner
d_inner_738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> [Integer] -> T_AllSeg_302
d_inner_738 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_inner_738 v1 v5 v6 v7
du_inner_738 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> [Integer] -> T_AllSeg_302
du_inner_738 v0 v1 v2 v3
  = coe
      C__'8759'__314 (coe du_sb'45'none_120)
      (coe
         du_allseg'45''43''43'_322 (coe v1)
         (coe
            d_ok'45'all_608 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__314 (coe du_sb'45'none_120)
            (coe C__'8759'__314 (coe du_sb'45'none_120) (coe C_'91''93'_306))))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_746 = erased
-- Once.CCC.Codegen.SlotBudget.segok-block
d_segok'45'block_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_segok'45'block_758 ~v0 v1 ~v2 ~v3 v4 v5
  = du_segok'45'block_758 v1 v4 v5
du_segok'45'block_758 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
du_segok'45'block_758 v0 v1 v2
  = coe C_mkSegOK_614 (coe du_inner_776 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotBudget._.inner
d_inner_776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> [Integer] -> T_AllSeg_302
d_inner_776 ~v0 v1 ~v2 ~v3 v4 v5 v6 = du_inner_776 v1 v4 v5 v6
du_inner_776 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> [Integer] -> T_AllSeg_302
du_inner_776 v0 v1 v2 v3
  = coe
      C__'8759'__314 (coe du_sb'45'none_120)
      (coe
         du_allseg'45''43''43'_322 (coe v1)
         (coe
            d_ok'45'all_608 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe C__'8759'__314 (coe du_sb'45'none_120) (coe C_'91''93'_306)))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_784 = erased
-- Once.CCC.Codegen.SlotBudget.BlockOK
d_BlockOK_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockOK_788 = erased
-- Once.CCC.Codegen.SlotBudget.segok-blocks
d_segok'45'blocks_798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_592
d_segok'45'blocks_798 ~v0 v1 v2 v3
  = du_segok'45'blocks_798 v1 v2 v3
du_segok'45'blocks_798 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_592
du_segok'45'blocks_798 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe
                du_segok'45'idle_620 (coe v1)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v2 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                             -> coe
                                  du_segok'45''43''43'_658
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214
                                           (coe v5) (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216
                                                 (coe v7)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                  (coe du_segok'45'block_758 (coe v0) (coe v8) (coe v11))
                                  (coe du_segok'45'blocks_798 (coe v0) (coe v4) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_822 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_cata'45'mono_822 v1 v3
du_cata'45'mono_822 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_822 v0 v1
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
d_frontier'45'mono_868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_868 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_868 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_frontier'45'mono_868 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   du_budget'45'of_72
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
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
                          d_frontier'45'mono_868 (coe v0) (coe v1) (coe v11) (coe v9)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                       (coe
                          d_frontier'45'mono_868 (coe v0) (coe v1) (coe v12) (coe v10)
                          (coe
                             du_budget'45'of_72
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9))))))
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
                       d_frontier'45'mono_868 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_frontier'45'mono_868 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          du_budget'45'of_72
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
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
      MAlonzo.Code.Once.IR.C_Cata_108 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           du_cata'45'mono_822
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v13)))
                           (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Out_118 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Ana_128 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C_const_150 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
      MAlonzo.Code.Once.IR.C_SigOp_156 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.lt-refl
d_lt'45'refl_1004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_1004 ~v0 v1 = du_lt'45'refl_1004 v1
du_lt'45'refl_1004 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lt'45'refl_1004 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_1012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_1012 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'nat'45'layer'45'below_1012 v4 v5
du_cata'45'nat'45'layer'45'below_1012 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_1012 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_154 (coe v0) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe v1) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_154 (coe v0) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe v1) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-body-below
d_cata'45'body'45'below_1042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'body'45'below_1042 v0 v1 ~v2 v3 ~v4 v5 v6
  = du_cata'45'body'45'below_1042 v0 v1 v3 v5 v6
du_cata'45'body'45'below_1042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
du_cata'45'body'45'below_1042 v0 v1 v2 v3 v4
  = coe
      du_segok'45'pre_698
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v2))))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (coe du_segok'45'thunk_718 (coe v1) (coe v3) (coe v4))
-- Once.CCC.Codegen.SlotBudget.cata-const-below
d_cata'45'const'45'below_1062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'const'45'below_1062 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_658
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
               (coe addInt (coe (2 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (1 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (2 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                         (coe v0) (coe v3)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
      (coe
         du_segok'45'idle_620
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                  (coe addInt (coe (2 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (1 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe v2))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                            (coe v0) (coe v3)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe du_ev'60'b_1090 (coe v2)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_154 (coe du_k'60'b_1088 (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_154 (coe du_pr'60'b_1092 (coe v2)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_ev'60'b_1090 (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154 (coe du_cl'60'b_1086 (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_154
                                                               (coe du_k'60'b_1088 (coe v2)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_120)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_120)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_154
                                                                        (coe
                                                                           du_k'60'b_1088 (coe v2))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_154
                                                                           (coe
                                                                              du_pr'60'b_1092
                                                                              (coe v2))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_120)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'slot_154
                                                                                 (coe
                                                                                    du_k'60'b_1088
                                                                                    (coe v2))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_120)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       du_sb'45'slot_154
                                                                                       (coe
                                                                                          du_cl'60'b_1086
                                                                                          (coe v2))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          du_sb'45'none_120)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                          (coe
                                                                                             du_sb'45'none_120)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                             (coe
                                                                                                du_sb'45'slot_154
                                                                                                (coe
                                                                                                   du_pr'60'b_1092
                                                                                                   (coe
                                                                                                      v2))
                                                                                                erased)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                (coe
                                                                                                   du_sb'45'none_120)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                   (coe
                                                                                                      du_sb'45'none_120)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))))))
      (coe
         du_cata'45'body'45'below_1042 (coe v0)
         (coe
            du_cata'45'budget'45'of_80
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
               (coe v0)
               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22)
               (coe v1) (coe v2) (coe v3) (coe v4)))
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_1080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_1080 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 = du_bnd_1080 v2 v6 v7
du_bnd_1080 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_1080 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v0 (addInt (coe (1 :: Integer)) (coe v1)) (4 :: Integer) v2)
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1086 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1086 v2
du_cl'60'b_1086 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1086 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
      (coe
         du_bnd_1080 (coe v0) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1088 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1088 v2
du_k'60'b_1088 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1088 v0
  = coe
      du_bnd_1080 (coe v0) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_1090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_1090 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_1090 v2
du_ev'60'b_1090 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_1090 v0
  = coe
      du_bnd_1080 (coe v0) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_1092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_1092 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_1092 v2
du_pr'60'b_1092 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_1092 v0
  = coe
      du_bnd_1080 (coe v0) (coe (3 :: Integer))
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
d_cata'45'nat'45'below_1124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'nat'45'below_1124 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_658
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
               (coe addInt (coe (4 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (4 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (6 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         du_segok'45'idle_620
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                  (coe addInt (coe (4 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (4 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (6 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_1154 (coe v2)))
      (coe
         du_segok'45''43''43'_658
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                                (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                                      (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                         (coe v0) (coe v3))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v3)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                            (coe (0 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                                                 (coe
                                                                                    (0 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
         (coe
            du_segok'45'idle_620
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                                   (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (3 :: Integer)) (coe v3)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                            (coe v0) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                               (coe v0)
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v3)))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                               (coe (0 :: Integer)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                                           (coe (2 :: Integer)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))))
            (coe du_I'8321'_1180 (coe v2)))
         (coe
            du_segok'45''43''43'_658
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                        (coe addInt (coe (5 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               du_segok'45'idle_620
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (2 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                (coe addInt (coe (5 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_1168 (coe v2)))
            (coe
               du_segok'45''43''43'_658
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                           (coe addInt (coe (4 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                              (coe addInt (coe (5 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                             (coe (1 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
               (coe
                  du_segok'45'idle_620
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                              (coe addInt (coe (4 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (5 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                    (coe v2))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                (coe (1 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
                  (coe du_I'8322'_1190 (coe v2)))
               (coe
                  du_segok'45''43''43'_658
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (3 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (5 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (3 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     du_segok'45'idle_620
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (5 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                      (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_1168 (coe v2)))
                  (coe
                     du_segok'45''43''43'_658
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (5 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        du_segok'45'idle_620
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (4 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                          (coe addInt (coe (5 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_1200))
                     (coe
                        du_cata'45'body'45'below_1042 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_80
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (7 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> Integer
d_b_1140 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_1140 v2
du_b_1140 :: Integer -> Integer
du_b_1140 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_1142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_1142 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p'60'b_1142 v2
du_p'60'b_1142 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_1142 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_1144 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_s'60'b_1144 v2
du_s'60'b_1144 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1144 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1146 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1146 v2
du_cl'60'b_1146 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1146 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1148 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1148 v2
du_k'60'b_1148 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1148 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_1150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_1150 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_1150 v2
du_ev'60'b_1150 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_1150 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_1152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_1152 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_1152 v2
du_pr'60'b_1152 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_1152 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1154 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_1154 v2
du_setup_1154 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1154 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_154 (coe du_ev'60'b_1150 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe du_k'60'b_1148 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_154 (coe du_pr'60'b_1152 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_154 (coe du_ev'60'b_1150 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_154 (coe du_cl'60'b_1146 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_154
                                                         (coe du_k'60'b_1148 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1168 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_1168 v2
du_call_1168 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1168 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_154 (coe du_k'60'b_1148 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe du_pr'60'b_1152 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe du_k'60'b_1148 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe du_cl'60'b_1146 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_pr'60'b_1152 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_1180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_1180 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_1180 v2
du_I'8321'_1180 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_1180 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_154
                                                               (coe du_p'60'b_1142 (coe v0)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_120)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_154
                                                                     (coe du_s'60'b_1144 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_120)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_120)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_120)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'slot_154
                                                                                 (coe
                                                                                    du_p'60'b_1142
                                                                                    (coe v0))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_120)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       du_sb'45'slot_154
                                                                                       (coe
                                                                                          du_s'60'b_1144
                                                                                          (coe v0))
                                                                                       erased)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          du_sb'45'none_120)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_1190 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_1190 v2
du_I'8322'_1190 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_1190 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe du_p'60'b_1142 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe du_s'60'b_1144 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_154 (coe du_p'60'b_1142 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154 (coe du_s'60'b_1144 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_1200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_1200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_1200
du_I'8323'_1200 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_1200
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.cata-linear-below
d_cata'45'linear'45'below_1210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'linear'45'below_1210 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_658
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
               (coe addInt (coe (8 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (8 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (4 :: Integer)) (coe v3))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (7 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         du_segok'45'idle_620
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                  (coe addInt (coe (8 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (8 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                            (coe v0)
                                                            (coe
                                                               addInt (coe (4 :: Integer))
                                                               (coe v3))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (7 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_1248 (coe v2)))
      (coe
         du_segok'45''43''43'_658
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (2 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v2)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v3))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_266
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
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
         (coe
            du_segok'45'idle_620
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                              (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe addInt (coe (5 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                   (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (5 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v2)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (2 ::
                                                                                          Integer))
                                                                                    (coe v2)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_266
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v3))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_266
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
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
            (coe du_I'8321'_1274 (coe v2)))
         (coe
            du_segok'45''43''43'_658
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (7 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                        (coe addInt (coe (9 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (6 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (9 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               du_segok'45'idle_620
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe addInt (coe (7 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (7 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                (coe addInt (coe (9 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_1262 (coe v2)))
            (coe
               du_segok'45''43''43'_658
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v3)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (4 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                       (coe addInt (coe (5 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                   (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                         (coe addInt (coe (5 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                                     (coe (2 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                        (coe v2))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                                              (coe (1 :: Integer)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v2)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
               (coe
                  du_segok'45'idle_620
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v3)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (3 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (4 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (3 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (5 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                           (coe v2))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                                                 (coe
                                                                                    (1 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v2)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                             (coe
                                                                                                v2))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
                  (coe du_I'8322'_1294 (coe v2)))
               (coe
                  du_segok'45''43''43'_658
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (7 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (9 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (7 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                          (coe addInt (coe (6 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     du_segok'45'idle_620
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (7 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (9 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (7 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                      (coe addInt (coe (9 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                     (coe du_call_1262 (coe v2)))
                  (coe
                     du_segok'45''43''43'_658
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe
                        du_segok'45'idle_620
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe du_I'8323'_1316))
                     (coe
                        du_cata'45'body'45'below_1042 (coe v0)
                        (coe
                           du_cata'45'budget'45'of_80
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
                              (coe v0)
                              (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26)
                              (coe v1) (coe v2) (coe v3) (coe v4)))
                        (coe addInt (coe (5 :: Integer)) (coe v3)) (coe v4) (coe v5)))))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> Integer
d_b_1226 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_b_1226 v2
du_b_1226 :: Integer -> Integer
du_b_1226 v0 = coe addInt (coe (10 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_1228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_1228 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p0_1228 v2
du_p0_1228 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_1228 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_1230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_1230 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p1_1230 v2
du_p1_1230 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_1230 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_1232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_1232 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p2_1232 v2
du_p2_1232 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_1232 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_1234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_1234 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p3_1234 v2
du_p3_1234 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_1234 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_1236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_1236 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p4_1236 v2
du_p4_1236 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_1236 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_1238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_1238 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_p5_1238 v2
du_p5_1238 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_1238 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.cl<b
d_cl'60'b_1240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b_1240 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl'60'b_1240 v2
du_cl'60'b_1240 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b_1240 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (7 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.k<b
d_k'60'b_1242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b_1242 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k'60'b_1242 v2
du_k'60'b_1242 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b_1242 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (8 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.ev<b
d_ev'60'b_1244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b_1244 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_ev'60'b_1244 v2
du_ev'60'b_1244 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b_1244 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (9 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.pr<b
d_pr'60'b_1246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b_1246 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_pr'60'b_1246 v2
du_pr'60'b_1246 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b_1246 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (10 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.setup
d_setup_1248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1248 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_setup_1248 v2
du_setup_1248 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1248 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_154 (coe du_ev'60'b_1244 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe du_k'60'b_1242 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_154 (coe du_pr'60'b_1246 (coe v0)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_154 (coe du_ev'60'b_1244 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_154 (coe du_cl'60'b_1240 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_154
                                                         (coe du_k'60'b_1242 (coe v0)) erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1262 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_call_1262 v2
du_call_1262 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1262 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_154 (coe du_k'60'b_1242 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe du_pr'60'b_1246 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe du_k'60'b_1242 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe du_cl'60'b_1240 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_pr'60'b_1246 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₁
d_I'8321'_1274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_1274 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8321'_1274 v2
du_I'8321'_1274 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_1274 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe du_p3_1234 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_p5_1238 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_154 (coe du_p2_1232 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_154 (coe du_p1_1230 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_154 (coe du_p5_1238 (coe v0))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_154
                                                            (coe du_p3_1234 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_120)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  du_sb'45'slot_154
                                                                  (coe du_p1_1230 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_154
                                                                     (coe du_p3_1234 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_154
                                                                        (coe du_p2_1232 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_120)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_120)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_120)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_120)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂
d_I'8322'_1294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_1294 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_I'8322'_1294 v2
du_I'8322'_1294 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_1294 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe du_p4_1236 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe du_p3_1234 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe du_p5_1238 (coe v0)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_154 (coe du_p3_1234 (coe v0)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_154 (coe du_p1_1230 (coe v0)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'slot_154 (coe du_p5_1238 (coe v0)) erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_154 (coe du_p4_1236 (coe v0))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_154
                                                            (coe du_p0_1228 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_120)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_120)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_120)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_154
                                                                        (coe du_p1_1230 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_120)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              du_sb'45'slot_154
                                                                              (coe
                                                                                 du_p0_1228
                                                                                 (coe v0))
                                                                              erased)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_120)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₃
d_I'8323'_1316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8323'_1316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_I'8323'_1316
du_I'8323'_1316 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8323'_1316
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.SlotBudget.push2-below
d_push2'45'below_1326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_1326 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_push2'45'below_1326 v5 v6 v7
du_push2'45'below_1326 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_1326 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_154 (coe v1) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe v2) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe v1) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_154 (coe v2) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe v0) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.pop2-below
d_pop2'45'below_1358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_1358 ~v0 ~v1 ~v2 v3 = du_pop2'45'below_1358 v3
du_pop2'45'below_1358 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_1358 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_154 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe v0) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.SlotBudget.wrap-sum-below
d_wrap'45'sum'45'below_1376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_1376 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_wrap'45'sum'45'below_1376 v4 v5
du_wrap'45'sum'45'below_1376 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_1376 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_154 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe v1) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_154 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_154 (coe v1) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
-- Once.CCC.Codegen.SlotBudget.visit-below
d_visit'45'below_1410 ::
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
d_visit'45'below_1410 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_visit'45'below_1410 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_visit'45'below_1410 ::
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
du_visit'45'below_1410 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_110 v11
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_120)
             (coe du_push2'45'below_1326 (coe v7) (coe v8) (coe v9))
      MAlonzo.Code.Once.Type.C__'8853'__114 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_120)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_120)
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
                   du_visit'45'below_1410 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11)))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1484 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_120)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_120)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_120)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                         (coe v0) (coe v2) (coe v3) (coe v4) (coe v11)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         du_visit'45'below_1410 (coe v0) (coe v11) (coe v2) (coe v3)
                         (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v7) (coe v8)
                         (coe v9) (coe du_recF_1480 (coe v11) (coe v12) (coe v5) (coe v10)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_154
                      (coe du_s'60'b_1520 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_120)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11))
                      (coe v6)))
                (coe
                   du_visit'45'below_1410 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v11))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1528 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_154
                         (coe du_s'60'b_1520 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_120)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_1410 (coe v0) (coe v11) (coe v2) (coe v3)
                      (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe du_recF_1524 (coe v11) (coe v12) (coe v5) (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1480 ::
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
d_recF_1480 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1480 v1 v2 v6 v12
du_recF_1480 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1480 v0 v1 v2 v3
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
d_recG_1484 ::
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
d_recG_1484 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1484 v1 v2 v6 v12
du_recG_1484 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1484 v0 v1 v2 v3
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
d_room4_1516 ::
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
d_room4_1516 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_room4_1516 v1 v2 v6 v12
du_room4_1516 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1516 v0 v1 v2 v3
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
d_s'60'b_1520 ::
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
d_s'60'b_1520 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_s'60'b_1520 v1 v2 v6 v12
du_s'60'b_1520 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1520 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1516 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1524 ::
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
d_recF_1524 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1524 v1 v2 v6 v12
du_recF_1524 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1524 v0 v1 v2 v3
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
d_recG_1528 ::
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
d_recG_1528 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1528 v1 v2 v6 v12
du_recG_1528 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1528 v0 v1 v2 v3
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
d_rebuild'45'below_1550 ::
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
d_rebuild'45'below_1550 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_rebuild'45'below_1550 v0 v1 v2 v5 v6 v8 v9
du_rebuild'45'below_1550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_1550 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_110 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_120)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe du_pop2'45'below_1358 (coe v5)
      MAlonzo.Code.Once.Type.C__'8853'__114 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_120)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_120)
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
                   du_rebuild'45'below_1550 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7)))
                      (coe v4))
                   (coe v5) (coe du_recG_1624 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                      (coe (1 :: Integer)) (coe v3))
                   (coe
                      du_wrap'45'sum'45'below_1376
                      (coe du_s'60'b_1612 (coe v7) (coe v8) (coe v3) (coe v6))
                      (coe du_b'45'ss_1616 (coe v7) (coe v8) (coe v3) (coe v6)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_120)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_120)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_120)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                            (coe v0) (coe v2) (coe v7)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            du_rebuild'45'below_1550 (coe v0) (coe v7) (coe v2)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5)
                            (coe du_recF_1620 (coe v7) (coe v8) (coe v3) (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_190
                               (coe (0 :: Integer)) (coe v3))
                            (coe
                               du_wrap'45'sum'45'below_1376
                               (coe du_s'60'b_1612 (coe v7) (coe v8) (coe v3) (coe v6))
                               (coe du_b'45'ss_1616 (coe v7) (coe v8) (coe v3) (coe v6)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_120)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_154
                      (coe du_s'60'b_1656 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_120)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_120)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                   (coe v0) (coe v2) (coe v7)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                (coe
                   du_rebuild'45'below_1550 (coe v0) (coe v7) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe du_recF_1676 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_154
                         (coe du_b'45'ss_1660 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_154
                            (coe du_s'60'b_1656 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_120)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_120)
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
                         du_rebuild'45'below_1550 (coe v0) (coe v8) (coe v2)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v7))
                            (coe v4))
                         (coe v5) (coe du_recG_1680 (coe v7) (coe v8) (coe v3) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_154
                            (coe du_b'45's2_1664 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_120)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  du_sb'45'slot_154
                                  (coe du_b'45's3_1670 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_120)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        du_sb'45'slot_154
                                        (coe du_b'45'ss_1660 (coe v7) (coe v8) (coe v3) (coe v6))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe du_sb'45'none_120)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              du_sb'45'slot_154
                                              (coe
                                                 du_b'45's2_1664 (coe v7) (coe v8) (coe v3)
                                                 (coe v6))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe du_sb'45'none_120)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe
                                                    du_sb'45'slot_154
                                                    (coe
                                                       du_b'45's3_1670 (coe v7) (coe v8) (coe v3)
                                                       (coe v6))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1608 ::
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
d_room4_1608 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1608 v1 v2 v6 v10
du_room4_1608 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1608 v0 v1 v2 v3
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
d_s'60'b_1612 ::
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
d_s'60'b_1612 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1612 v1 v2 v6 v10
du_s'60'b_1612 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1612 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1608 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1616 ::
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
d_b'45'ss_1616 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1616 v1 v2 v6 v10
du_b'45'ss_1616 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1616 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1608 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1620 ::
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
d_recF_1620 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1620 v1 v2 v6 v10
du_recF_1620 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1620 v0 v1 v2 v3
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
d_recG_1624 ::
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
d_recG_1624 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1624 v1 v2 v6 v10
du_recG_1624 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1624 v0 v1 v2 v3
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
d_room4_1652 ::
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
d_room4_1652 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1652 v1 v2 v6 v10
du_room4_1652 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1652 v0 v1 v2 v3
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
d_s'60'b_1656 ::
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
d_s'60'b_1656 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1656 v1 v2 v6 v10
du_s'60'b_1656 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1656 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1652 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1660 ::
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
d_b'45'ss_1660 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1660 v1 v2 v6 v10
du_b'45'ss_1660 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1660 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1652 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_1664 ::
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
d_b'45's2_1664 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's2_1664 v1 v2 v6 v10
du_b'45's2_1664 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_1664 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_1652 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_1670 ::
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
d_b'45's3_1670 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's3_1670 v1 v2 v6 v10
du_b'45's3_1670 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_1670 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_1652 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1676 ::
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
d_recF_1676 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1676 v1 v2 v6 v10
du_recF_1676 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1676 v0 v1 v2 v3
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
d_recG_1680 ::
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
d_recG_1680 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1680 v1 v2 v6 v10
du_recG_1680 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1680 v0 v1 v2 v3
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
d_visit'45'idle_1712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_1712 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1774 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'branching'45'below_1834 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_segok'45''43''43'_658
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                (coe (0 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_266
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
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
      (coe
         du_segok'45'idle_620
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266
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
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
         (coe du_setup_1872 (coe v1) (coe v3)))
      (coe
         du_segok'45''43''43'_658
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
            (coe v0) (coe v1) (coe v3) (coe v4))
         (coe
            du_segok'45'weaken_686 (coe du_b_1852 (coe v1) (coe v3))
            (coe
               du_cata'45'budget'45'of_80
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
            (coe du_b'8804'b2_1854 (coe v1) (coe v3))
            (coe
               du_segok'45'idle_620
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
                  (coe v0) (coe v1) (coe v3) (coe v4))
               (coe du_I'8321''45'all_1932 (coe v0) (coe v1) (coe v3) (coe v4))))
         (coe
            du_segok'45''43''43'_658
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe
               du_segok'45'idle_620
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
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
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
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
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
               (coe du_call_1886 (coe v1) (coe v3)))
            (coe
               du_segok'45''43''43'_658
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                  (coe v0) (coe v3) (coe v4))
               (coe
                  du_segok'45'weaken_686 (coe du_b_1852 (coe v1) (coe v3))
                  (coe
                     du_cata'45'budget'45'of_80
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
                  (coe du_b'8804'b2_1854 (coe v1) (coe v3))
                  (coe
                     du_segok'45'idle_620
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                        (coe v0) (coe v3) (coe v4))
                     (coe du_I'8322''45'all_1966 (coe v1) (coe v3))))
               (coe
                  du_cata'45'body'45'below_1042 (coe v0)
                  (coe
                     du_cata'45'budget'45'of_80
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
d_b_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> Integer
d_b_1852 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_b_1852 v1 v3
du_b_1852 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_b_1852 v0 v1
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
d_b'8804'b2_1854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'8804'b2_1854 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_b'8804'b2_1854 v1 v3
du_b'8804'b2_1854 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'8804'b2_1854 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe du_b_1852 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.bnd
d_bnd_1858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_1858 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_bnd_1858 v1 v3 v7 v8
du_bnd_1858 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_1858 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe addInt (coe (1 :: Integer)) (coe du_b_1852 (coe v0) (coe v1)))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (coe du_b_1852 (coe v0) (coe v1))
         (addInt (coe (1 :: Integer)) (coe v2)) (4 :: Integer) v3)
-- Once.CCC.Codegen.SlotBudget._.cl<b2
d_cl'60'b2_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cl'60'b2_1864 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_cl'60'b2_1864 v1 v3
du_cl'60'b2_1864 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cl'60'b2_1864 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_b_1852 (coe v0) (coe v1))))
      (coe
         du_bnd_1858 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.k<b2
d_k'60'b2_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'b2_1866 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_k'60'b2_1866 v1 v3
du_k'60'b2_1866 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'b2_1866 v0 v1
  = coe
      du_bnd_1858 (coe v0) (coe v1) (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
-- Once.CCC.Codegen.SlotBudget._.ev<b2
d_ev'60'b2_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ev'60'b2_1868 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_ev'60'b2_1868 v1 v3
du_ev'60'b2_1868 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ev'60'b2_1868 v0 v1
  = coe
      du_bnd_1858 (coe v0) (coe v1) (coe (2 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.SlotBudget._.pr<b2
d_pr'60'b2_1870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pr'60'b2_1870 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_pr'60'b2_1870 v1 v3
du_pr'60'b2_1870 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pr'60'b2_1870 v0 v1
  = coe
      du_bnd_1858 (coe v0) (coe v1) (coe (3 :: Integer))
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
d_setup_1872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_setup_1872 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_setup_1872 v1 v3
du_setup_1872 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_setup_1872 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            du_sb'45'slot_154 (coe du_ev'60'b2_1868 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe
                  du_sb'45'slot_154 (coe du_k'60'b2_1866 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe
                        du_sb'45'slot_154 (coe du_pr'60'b2_1870 (coe v0) (coe v1)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              du_sb'45'slot_154 (coe du_ev'60'b2_1868 (coe v0) (coe v1)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_154 (coe du_cl'60'b2_1864 (coe v0) (coe v1))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_154
                                                         (coe du_k'60'b2_1866 (coe v0) (coe v1))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.call
d_call_1886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_call_1886 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_call_1886 v1 v3
du_call_1886 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_call_1886 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_120)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            du_sb'45'slot_154 (coe du_k'60'b2_1866 (coe v0) (coe v1)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe
               du_sb'45'slot_154 (coe du_pr'60'b2_1870 (coe v0) (coe v1)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe
                     du_sb'45'slot_154 (coe du_k'60'b2_1866 (coe v0) (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe
                           du_sb'45'slot_154 (coe du_cl'60'b2_1864 (coe v0) (coe v1)) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154 (coe du_pr'60'b2_1870 (coe v0) (coe v1))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1898 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7_1898 v1 v3
du_fixed7_1898 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1898 v0 v1
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
d_fixed7''_1900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1900 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_fixed7''_1900 v1 v3
du_fixed7''_1900 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1900 v0 v1 = coe du_fixed7_1898 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1904 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q0_1904 v1 v3
du_q0_1904 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1904 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1906 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q1_1906 v1 v3
du_q1_1906 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1906 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1908 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q2_1908 v1 v3
du_q2_1908 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1908 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1912 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q3_1912 v1 v3
du_q3_1912 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1912 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1916 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q4_1916 v1 v3
du_q4_1916 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1916 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1920 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q5_1920 v1 v3
du_q5_1920 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1920 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1924 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_q6_1924 v1 v3
du_q6_1924 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1924 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1900 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1928 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_walk'45'room_1928 v1 v3
du_walk'45'room_1928 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1928 v0 v1
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
d_I'8321''45'idle_1930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1930 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1932 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_I'8321''45'all_1932 v0 v1 v3 v4
du_I'8321''45'all_1932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1932 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_154 (coe du_q3_1912 (coe v1) (coe v2)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe du_q6_1924 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_154 (coe du_q6_1924 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_q1_1906 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_154 (coe du_q6_1924 (coe v1) (coe v2)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154 (coe du_q2_1908 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154 (coe du_q6_1924 (coe v1) (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_154 (coe du_q0_1904 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_154
                                                   (coe du_q3_1912 (coe v1) (coe v2)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            du_push2'45'below_1326 (coe du_q0_1904 (coe v1) (coe v2))
            (coe du_q4_1916 (coe v1) (coe v2))
            (coe du_q5_1920 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_120)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_154 (coe du_q0_1904 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_154 (coe du_q0_1904 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154 (coe du_q3_1912 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154 (coe du_q3_1912 (coe v1) (coe v2))
                                             erased)
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
                  du_push2'45'below_1326 (coe du_q1_1906 (coe v1) (coe v2))
                  (coe du_q4_1916 (coe v1) (coe v2))
                  (coe du_q5_1920 (coe v1) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_154 (coe du_q3_1912 (coe v1) (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_120)
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
                        du_visit'45'below_1410 (coe v0) (coe v1) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3))
                        (coe du_q0_1904 (coe v1) (coe v2))
                        (coe du_q4_1916 (coe v1) (coe v2))
                        (coe du_q5_1920 (coe v1) (coe v2))
                        (coe du_walk'45'room_1928 (coe v1) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_120)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_154 (coe du_q1_1906 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_154 (coe du_q1_1906 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
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
                                 du_rebuild'45'below_1550 (coe v0) (coe v1)
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
                                 (coe du_q2_1908 (coe v1) (coe v2))
                                 (coe du_walk'45'room_1928 (coe v1) (coe v2)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_120)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1966 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_I'8322''45'all_1966 v1 v3
du_I'8322''45'all_1966 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1966 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_172
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_1326 (coe du_q2_1908 (coe v0) (coe v1))
         (coe du_q4_1916 (coe v0) (coe v1))
         (coe du_q5_1920 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_120)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_120)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_154 (coe du_q2_1908 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_120)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_120)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_SegOK_592 -> T_SegOK_592
d_cata'45'slots'45'below_1980 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             d_cata'45'const'45'below_1062 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             d_cata'45'nat'45'below_1124 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             d_cata'45'linear'45'below_1210 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             d_cata'45'branching'45'below_1834 (coe v0) (coe v7) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_2034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer -> T_SegOK_592
d_slots'45'below_2034 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v1) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             du_segok'45''43''43'_658
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                du_segok'45'weaken_686
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_budget'45'of_72
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10)))
                (coe
                   du_trace'45'of_76
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   d_frontier'45'mono_868 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
                (coe
                   d_slots'45'below_2034 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                   (coe v5)))
             (coe
                du_segok'45'pre_698
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_120)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_2034 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    du_segok'45'pre_698
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                             (coe v4))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             du_sb'45'slot_154
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                   (coe addInt (coe (1 :: Integer)) (coe v4)))
                                (coe
                                   d_h_2076 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9) (coe v10)
                                   (coe v4) (coe v5)))
                             erased)
                          (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                    (coe
                       du_segok'45''43''43'_658
                       (coe
                          du_trace'45'of_76
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          du_segok'45'weaken_686
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             du_budget'45'of_72
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10)))
                          (coe
                             du_trace'45'of_76
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                          (coe
                             d_frontier'45'mono_868 (coe v0) (coe v1) (coe v12) (coe v10)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                      (coe v9)))))
                          (coe
                             d_slots'45'below_2034 (coe v0) (coe v1) (coe v11) (coe v9)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)))
                       (coe
                          du_segok'45'pre_698
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238
                                   (coe v4))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe
                                du_sb'45'slot_154
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   (coe
                                      d_h_2076 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                      (coe v10) (coe v4) (coe v5)))
                                erased)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   du_sb'45'slot_154
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                      (coe
                                         d_h_2076 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                         (coe v10) (coe v4) (coe v5)))
                                   erased)
                                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                          (coe
                             du_segok'45''43''43'_658
                             (coe
                                du_trace'45'of_76
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v1) (coe v12)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                            (coe v0) (coe v1) (coe v11)
                                            (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                            (coe v9))))
                                   (coe v10)))
                             (coe
                                d_slots'45'below_2034 (coe v0) (coe v1) (coe v12) (coe v10)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                         (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                         (coe v9)))))
                             (coe
                                du_segok'45'idle_620
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                         (coe (2 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                            (coe addInt (coe (3 :: Integer)) (coe v4)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                              (coe
                                                                 addInt (coe (3 :: Integer))
                                                                 (coe v4)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      du_sb'45'slot_154
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                            (coe addInt (coe (3 :: Integer)) (coe v4)))
                                         (coe
                                            d_h_2076 (coe v0) (coe v1) (coe v11) (coe v12) (coe v9)
                                            (coe v10) (coe v4) (coe v5)))
                                      erased)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe du_sb'45'none_120)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe
                                            du_sb'45'slot_154
                                            (coe
                                               d_h_2076 (coe v0) (coe v1) (coe v11) (coe v12)
                                               (coe v9) (coe v10) (coe v4) (coe v5))
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe du_sb'45'none_120)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe
                                                  du_sb'45'slot_154
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     (coe
                                                        d_h_2076 (coe v0) (coe v1) (coe v11)
                                                        (coe v12) (coe v9) (coe v10) (coe v4)
                                                        (coe v5)))
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe du_sb'45'none_120)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                     (coe
                                                        du_sb'45'slot_154
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 addInt (coe (3 :: Integer))
                                                                 (coe v4)))
                                                           (coe
                                                              d_h_2076 (coe v0) (coe v1) (coe v11)
                                                              (coe v12) (coe v9) (coe v10) (coe v4)
                                                              (coe v5)))
                                                        erased)
                                                     (coe
                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                        (coe du_sb'45'none_120)
                                                        (coe
                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                           (coe
                                                              du_sb'45'slot_154
                                                              (coe
                                                                 d_h_2076 (coe v0) (coe v1)
                                                                 (coe v11) (coe v12) (coe v9)
                                                                 (coe v10) (coe v4) (coe v5))
                                                              erased)
                                                           (coe
                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v9))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_fst_44)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_snd_50)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_620
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154
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
                           du_segok'45'idle_620
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_154
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_154
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
                           du_segok'45'idle_620
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_154
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
                           du_segok'45'idle_620
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_154
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_120)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_154
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_120)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_154
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
                    du_segok'45'pre_698
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe du_sb'45'none_120)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_120)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       du_segok'45''43''43'_658
                       (coe
                          du_trace'45'of_76
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v12) (coe v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                             (coe v10)))
                       (coe
                          d_slots'45'below_2034 (coe v0) (coe v12) (coe v2) (coe v10)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                       (coe
                          du_segok'45'pre_698
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0) (coe v5))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_120)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe du_sb'45'none_120)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_120)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe du_sb'45'none_120)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                          (coe
                             du_segok'45''43''43'_658
                             (coe
                                du_trace'45'of_76
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                du_segok'45'weaken_686
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   du_budget'45'of_72
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                      (coe MAlonzo.Code.Once.IR.C_case_70 v9 v10)))
                                (coe
                                   du_trace'45'of_76
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   d_frontier'45'mono_868 (coe v0) (coe v12) (coe v2) (coe v10)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                         (coe v0) (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                            (coe v0) (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                                (coe
                                   d_slots'45'below_2034 (coe v0) (coe v11) (coe v2) (coe v9)
                                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5))))
                             (coe
                                du_segok'45'idle_620
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_266 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_120)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_terminal_74)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v2) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_initial_78)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v10 of
             MAlonzo.Code.Once.IR.C_Stack_6
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             du_sb'45'slot_154
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_120)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   du_sb'45'slot_154
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   erased)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe
                                      du_sb'45'slot_154
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
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             du_sb'45'slot_154
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                             erased)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_120)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe
                                   du_sb'45'slot_154
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                   erased)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_120)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe
                                         du_sb'45'slot_154
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                            (coe addInt (coe (1 :: Integer)) (coe v4)))
                                         erased)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe du_sb'45'none_120)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                            (coe du_sb'45'none_120)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe du_sb'45'none_120)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                  (coe
                                                     du_sb'45'slot_154
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                      -> coe
                           du_segok'45'idle_620
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v10) (coe v2))
                                    (coe v10))
                                 (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_120)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_154
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_120)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_120)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_120)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_120)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_154
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_120)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_154
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v4)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_120)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_154
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v4)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_120)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_154
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v4)))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_120)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_154
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
                                                                           (coe du_sb'45'none_120)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_120)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_108 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           d_cata'45'slots'45'below_1980 (coe v0)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v13)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13)
                                       (coe v2)))
                                 (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13)
                                          (coe v2)))
                                    (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v5) (coe v10)))))
                           (coe
                              d_slots'45'below_2034 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13)
                                    (coe v2)))
                              (coe v2) (coe v10) (coe (0 :: Integer)) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v7 v9
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Para_114 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Out_118 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_Out_118 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_122 v7 v8)))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_128 v7 v9
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_128 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v6
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4) (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_const_150 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_528
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_150 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_530
               -> coe
                    du_segok'45'idle_620
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_150 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_120)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_156 v6 v7 v8
        -> coe
             du_segok'45'idle_620
             (coe
                du_trace'45'of_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v6))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v7)) (coe v4)
                   (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_120)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_2076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_2076 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_868 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_868 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_72
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget.trace-lookup
d_trace'45'lookup_2244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_trace'45'lookup_2244 ~v0 v1 v2 = du_trace'45'lookup_2244 v1 v2
du_trace'45'lookup_2244 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_trace'45'lookup_2244 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_trace'45'lookup_2244 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.fetch-at
d_fetch'45'at_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch'45'at_2252 ~v0 = du_fetch'45'at_2252
du_fetch'45'at_2252 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch'45'at_2252 = coe du_trace'45'lookup_2244
-- Once.CCC.Codegen.SlotBudget.seg-at
d_seg'45'at_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> T_SegState_224 -> T_SegState_224
d_seg'45'at_2254 ~v0 v1 v2 v3 = du_seg'45'at_2254 v1 v2 v3
du_seg'45'at_2254 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> T_SegState_224 -> T_SegState_224
du_seg'45'at_2254 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       du_seg'45'at_2254 (coe v5) (coe v3)
                       (coe du_seg'45'step_266 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotBudget.seg-at-suc
d_seg'45'at'45'suc_2276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_SegState_224 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_2276 = erased
-- Once.CCC.Codegen.SlotBudget.idle-seg-at
d_idle'45'seg'45'at_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_2304 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_2338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  T_SegState_224 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_2338 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_2374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  T_SegState_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_2374 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ˡ
d_fetch'45''43''43''737'_2398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_2398 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ʳ
d_fetch'45''43''43''691'_2426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_2426 = erased
-- Once.CCC.Codegen.SlotBudget.split-pos
d_split'45'pos_2446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_2446 ~v0 v1 v2 = du_split'45'pos_2446 v1 v2
du_split'45'pos_2446 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split'45'pos_2446 v0 v1
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
                    (let v5 = coe du_split'45'pos_2446 (coe v3) (coe v4) in
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
d_allseg'45'at_2490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_224 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  T_AllSeg_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_92
d_allseg'45'at_2490 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_allseg'45'at_2490 v2 v3 v5
du_allseg'45'at_2490 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> T_AllSeg_302 -> T_SlotBelow_92
du_allseg'45'at_2490 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__314 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__314 v9 v10
                         -> coe du_allseg'45'at_2490 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.bodies-of
d_bodies'45'of_2514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bodies'45'of_2514 ~v0 v1 = du_bodies'45'of_2514 v1
du_bodies'45'of_2514 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bodies'45'of_2514 v0
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
d_blocks'45'below_2528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'below_2528 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_bodies'45'of_2514
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                d_blocks'45'below_2528 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_blocks'45'below_2528 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bodies'45'of_2514
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v1) (coe v11)
                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                    (coe
                       d_blocks'45'below_2528 (coe v0) (coe v1) (coe v11) (coe v9)
                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       d_blocks'45'below_2528 (coe v0) (coe v1) (coe v12) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v1) (coe v11)
                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> coe
             seq (coe v8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_inr_62 v8
        -> coe
             seq (coe v8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bodies'45'of_2514
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v11) (coe v2) (coe v4)
                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                    (coe
                       d_blocks'45'below_2528 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_blocks'45'below_2528 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (d_slots'45'below_2034
                          (coe v0)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                          (coe v12) (coe v9) (coe (0 :: Integer))
                          (coe addInt (coe (2 :: Integer)) (coe v5)))
                       (d_blocks'45'below_2528
                          (coe v0)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                          (coe v12) (coe v9) (coe (0 :: Integer))
                          (coe addInt (coe (2 :: Integer)) (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Cata_108 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           d_blocks'45'below_2528 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13) (coe v2)))
                           (coe v2) (coe v10) (coe (0 :: Integer)) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v7 v9
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Out_118 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v7 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Ana_128 v7 v9
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v6
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_const_150 v7 v8
        -> coe
             seq (coe v7)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_SigOp_156 v6 v7 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-all
d_ir'45'slots'45'below'45'all_2668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_AllSeg_302
d_ir'45'slots'45'below'45'all_2668 v0 v1 v2 v3
  = coe
      du_allseg'45''43''43'_322
      (coe
         du_trace'45'of_76
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
            (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3)))
      (coe
         d_ok'45'all_608
         (d_slots'45'below_2034
            (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         C__'8759'__314 (coe du_sb'45'none_120)
         (coe
            d_ok'45'all_608
            (coe
               du_segok'45'blocks_798
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_742
                  (coe v0) (coe v1) (coe v2) (coe v3))
               (coe
                  du_bodies'45'of_2514
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                     (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                     (coe (0 :: Integer)) (coe v3)))
               (coe
                  d_blocks'45'below_2528 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe (0 :: Integer)) (coe (0 :: Integer))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.SlotBudget.emitted-slot-seg
d_emitted'45'slot'45'seg_2686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_2686 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_emitted'45'slot'45'seg_2686 v0 v1 v2 v3 v4 v6
du_emitted'45'slot'45'seg_2686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_2686 v0 v1 v2 v3 v4 v5
  = coe
      d_below_108
      (coe
         du_allseg'45'at_2490
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4)
         (coe
            d_ir'45'slots'45'below'45'all_2668 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      v5 erased
