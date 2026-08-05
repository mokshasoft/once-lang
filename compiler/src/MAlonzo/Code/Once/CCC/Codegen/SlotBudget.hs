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
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₁
d_cata'45'br'45'I'8321'_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_cata'45'br'45'I'8321'_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_292
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-br-I₂
d_cata'45'br'45'I'8322'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_cata'45'br'45'I'8322'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_300
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-dispatch
d_cata'45'dispatch_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_316
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.cata-nat-layer
d_cata'45'nat'45'layer_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_cata'45'nat'45'layer_20 ~v0 = du_cata'45'nat'45'layer_20
du_cata'45'nat'45'layer_20 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_cata'45'nat'45'layer_20
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'nat'45'layer_64
-- Once.CCC.Codegen.SlotBudget._.fsize
d_fsize_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
d_fsize_24 ~v0 = du_fsize_24
du_fsize_24 :: MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
du_fsize_24
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122
-- Once.CCC.Codegen.SlotBudget._.ir-stack-budget
d_ir'45'stack'45'budget_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_26 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace
d_ir'45'to'45'trace_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_ir'45'to'45'trace_28 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.ir-to-trace'
d_ir'45'to'45'trace''_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_30 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.pop2
d_pop2_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_pop2_34 ~v0 = du_pop2_34
du_pop2_34 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_pop2_34
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_148
-- Once.CCC.Codegen.SlotBudget._.push2
d_push2_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_push2_36 ~v0 = du_push2_36
du_push2_36 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_push2_36
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_138
-- Once.CCC.Codegen.SlotBudget._.rebuild-walk
d_rebuild'45'walk_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_rebuild'45'walk_38 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.SlotBudget._.visit-walk
d_visit'45'walk_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_visit'45'walk_48 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_182
      (coe v0)
-- Once.CCC.Codegen.SlotBudget._.wrap-sum
d_wrap'45'sum_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_wrap'45'sum_50 ~v0 = du_wrap'45'sum_50
du_wrap'45'sum_50 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_wrap'45'sum_50
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_156
-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_62 ~v0 v1 = du_budget'45'of_62 v1
du_budget'45'of_62 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_62 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_trace'45'of_66 ~v0 v1 = du_trace'45'of_66 v1
du_trace'45'of_66 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_trace'45'of_66 v0
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
d_cata'45'budget'45'of_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_70 ~v0 v1 = du_cata'45'budget'45'of_70 v1
du_cata'45'budget'45'of_70 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_cata'45'budget'45'of_70 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_cata'45'trace'45'of_74 ~v0 v1 = du_cata'45'trace'45'of_74 v1
du_cata'45'trace'45'of_74 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_cata'45'trace'45'of_74 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow
d_SlotBelow_82 a0 a1 a2 = ()
data T_SlotBelow_82
  = C_mkSlotBelow_104 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.SlotBudget.SlotBelow.below
d_below_98 ::
  T_SlotBelow_82 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_98 v0
  = case coe v0 of
      C_mkSlotBelow_104 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow.pair-below
d_pair'45'below_102 ::
  T_SlotBelow_82 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pair'45'below_102 v0
  = case coe v0 of
      C_mkSlotBelow_104 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-none
d_sb'45'none_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_82
d_sb'45'none_110 ~v0 ~v1 ~v2 ~v3 = du_sb'45'none_110
du_sb'45'none_110 :: T_SlotBelow_82
du_sb'45'none_110
  = coe
      C_mkSlotBelow_104 (coe (\ v0 v1 -> coe du_go_126))
      (coe (\ v0 v1 -> coe du_go_126))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_go_126
du_go_126 :: AgdaAny
du_go_126 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-slot
d_sb'45'slot_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_82
d_sb'45'slot_144 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_sb'45'slot_144 v5 v6
du_sb'45'slot_144 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_82
du_sb'45'slot_144 v0 v1
  = coe C_mkSlotBelow_104 (coe (\ v2 v3 -> v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.just-inj
d_just'45'inj_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_162 = erased
-- Once.CCC.Codegen.SlotBudget.sb-weaken
d_sb'45'weaken_176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_176 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sb'45'weaken_176 v3 v4 v5
du_sb'45'weaken_176 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sb'45'weaken_176 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       C_mkSlotBelow_104
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_below_98 v5 v9 erased) (coe v1)))
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_pair'45'below_102 v5 v9 erased) (coe v1))))
                    (coe du_sb'45'weaken_176 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-le
d_sb'45'le_200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_82 -> T_SlotBelow_82
d_sb'45'le_200 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sb'45'le_200 v4 v5
du_sb'45'le_200 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_82 -> T_SlotBelow_82
du_sb'45'le_200 v0 v1
  = coe
      C_mkSlotBelow_104
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_below_98 v1 v2 erased) (coe v0)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_pair'45'below_102 v1 v2 erased) (coe v0)))
-- Once.CCC.Codegen.SlotBudget.SegState
d_SegState_214 a0 = ()
data T_SegState_214 = C_mkSeg_224 Integer [Integer]
-- Once.CCC.Codegen.SlotBudget.SegState.cur
d_cur_220 :: T_SegState_214 -> Integer
d_cur_220 v0
  = case coe v0 of
      C_mkSeg_224 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegState.saved
d_saved_222 :: T_SegState_214 -> [Integer]
d_saved_222 v0
  = case coe v0 of
      C_mkSeg_224 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegAction
d_SegAction_226 a0 = ()
data T_SegAction_226
  = C_seg'45'id_228 | C_seg'45'push_230 Integer | C_seg'45'pop_232
-- Once.CCC.Codegen.SlotBudget.seg-action
d_seg'45'action_234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegAction_226
d_seg'45'action_234 ~v0 v1 = du_seg'45'action_234 v1
du_seg'45'action_234 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegAction_226
du_seg'45'action_234 v0
  = let v1 = coe C_seg'45'id_228 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v3 v4
                  -> coe C_seg'45'push_230 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v3
                  -> coe C_seg'45'pop_232
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotBudget.pop-with
d_pop'45'with_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SegState_214 -> T_SegState_214
d_pop'45'with_238 ~v0 v1 v2 = du_pop'45'with_238 v1 v2
du_pop'45'with_238 :: [Integer] -> T_SegState_214 -> T_SegState_214
du_pop'45'with_238 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_224 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply
d_seg'45'apply_246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_226 -> T_SegState_214 -> T_SegState_214
d_seg'45'apply_246 ~v0 v1 v2 = du_seg'45'apply_246 v1 v2
du_seg'45'apply_246 ::
  T_SegAction_226 -> T_SegState_214 -> T_SegState_214
du_seg'45'apply_246 v0 v1
  = case coe v0 of
      C_seg'45'id_228 -> coe v1
      C_seg'45'push_230 v2
        -> coe
             C_mkSeg_224 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_220 (coe v1)) (coe d_saved_222 (coe v1)))
      C_seg'45'pop_232
        -> coe du_pop'45'with_238 (coe d_saved_222 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-step
d_seg'45'step_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegState_214 -> T_SegState_214
d_seg'45'step_256 ~v0 v1 v2 = du_seg'45'step_256 v1 v2
du_seg'45'step_256 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegState_214 -> T_SegState_214
du_seg'45'step_256 v0 v1
  = coe
      du_seg'45'apply_246 (coe du_seg'45'action_234 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget.seg-fold
d_seg'45'fold_262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegState_214 -> T_SegState_214
d_seg'45'fold_262 ~v0 v1 v2 = du_seg'45'fold_262 v1 v2
du_seg'45'fold_262 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegState_214 -> T_SegState_214
du_seg'45'fold_262 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_seg'45'fold_262 (coe v3)
             (coe du_seg'45'step_256 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-fold-++
d_seg'45'fold'45''43''43'_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_278 = erased
-- Once.CCC.Codegen.SlotBudget.AllSeg
d_AllSeg_292 a0 a1 a2 = ()
data T_AllSeg_292
  = C_'91''93'_296 | C__'8759'__304 T_SlotBelow_82 T_AllSeg_292
-- Once.CCC.Codegen.SlotBudget.allseg-++
d_allseg'45''43''43'_312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_214 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_292 -> T_AllSeg_292 -> T_AllSeg_292
d_allseg'45''43''43'_312 ~v0 ~v1 v2 ~v3 v4 v5
  = du_allseg'45''43''43'_312 v2 v4 v5
du_allseg'45''43''43'_312 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_292 -> T_AllSeg_292 -> T_AllSeg_292
du_allseg'45''43''43'_312 v0 v1 v2
  = case coe v1 of
      C_'91''93'_296 -> coe v2
      C__'8759'__304 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__304 v6
                    (coe du_allseg'45''43''43'_312 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.allseg-++bal
d_allseg'45''43''43'bal_328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_214 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_292 -> T_AllSeg_292 -> T_AllSeg_292
d_allseg'45''43''43'bal_328 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_allseg'45''43''43'bal_328 v2 v5 v6
du_allseg'45''43''43'bal_328 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_292 -> T_AllSeg_292 -> T_AllSeg_292
du_allseg'45''43''43'bal_328 v0 v1 v2
  = coe du_allseg'45''43''43'_312 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotBudget.SavedLE
d_SavedLE_338 a0 a1 a2 = ()
data T_SavedLE_338
  = C_'91''93'_340 |
    C__'8759'__350 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_338
-- Once.CCC.Codegen.SlotBudget.SegLE
d_SegLE_356 a0 a1 a2 = ()
data T_SegLE_356
  = C_mkSegLE_370 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_338
-- Once.CCC.Codegen.SlotBudget.SegLE.cur-le
d_cur'45'le_366 ::
  T_SegLE_356 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_366 v0
  = case coe v0 of
      C_mkSegLE_370 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegLE.saved-le
d_saved'45'le_368 :: T_SegLE_356 -> T_SavedLE_338
d_saved'45'le_368 v0
  = case coe v0 of
      C_mkSegLE_370 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.saved-le-refl
d_saved'45'le'45'refl_374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [Integer] -> T_SavedLE_338
d_saved'45'le'45'refl_374 ~v0 v1 = du_saved'45'le'45'refl_374 v1
du_saved'45'le'45'refl_374 :: [Integer] -> T_SavedLE_338
du_saved'45'le'45'refl_374 v0
  = case coe v0 of
      [] -> coe C_'91''93'_340
      (:) v1 v2
        -> coe
             C__'8759'__350
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (coe du_saved'45'le'45'refl_374 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.pop-mono
d_pop'45'mono_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_214 ->
  T_SegState_214 ->
  [Integer] ->
  [Integer] -> T_SavedLE_338 -> T_SegLE_356 -> T_SegLE_356
d_pop'45'mono_388 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pop'45'mono_388 v3 v4 v5 v6
du_pop'45'mono_388 ::
  [Integer] ->
  [Integer] -> T_SavedLE_338 -> T_SegLE_356 -> T_SegLE_356
du_pop'45'mono_388 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__350 v10 v11 -> coe C_mkSegLE_370 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply-mono
d_seg'45'apply'45'mono_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_226 ->
  T_SegState_214 -> T_SegState_214 -> T_SegLE_356 -> T_SegLE_356
d_seg'45'apply'45'mono_410 ~v0 v1 v2 v3 v4
  = du_seg'45'apply'45'mono_410 v1 v2 v3 v4
du_seg'45'apply'45'mono_410 ::
  T_SegAction_226 ->
  T_SegState_214 -> T_SegState_214 -> T_SegLE_356 -> T_SegLE_356
du_seg'45'apply'45'mono_410 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_228 -> coe v3
      C_seg'45'push_230 v4
        -> coe
             C_mkSegLE_370
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_220 (coe du_seg'45'apply_246 (coe v0) (coe v1))))
             (coe
                C__'8759'__350 (d_cur'45'le_366 (coe v3))
                (d_saved'45'le_368 (coe v3)))
      C_seg'45'pop_232
        -> coe
             du_pop'45'mono_388 (coe d_saved_222 (coe v1))
             (coe d_saved_222 (coe v2)) (coe d_saved'45'le_368 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken
d_seg'45'weaken_430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_214 ->
  T_SegState_214 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegLE_356 -> T_AllSeg_292 -> T_AllSeg_292
d_seg'45'weaken_430 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken_430 v1 v2 v3 v4 v5
du_seg'45'weaken_430 ::
  T_SegState_214 ->
  T_SegState_214 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegLE_356 -> T_AllSeg_292 -> T_AllSeg_292
du_seg'45'weaken_430 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_296 -> coe C_'91''93'_296
      C__'8759'__304 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__304
                    (coe du_sb'45'le_200 (coe d_cur'45'le_366 (coe v3)) (coe v8))
                    (coe
                       du_seg'45'weaken_430
                       (coe
                          du_seg'45'apply_246 (coe du_seg'45'action_234 (coe v10)) (coe v0))
                       (coe du_seg'45'step_256 (coe v10) (coe v1)) (coe v11)
                       (coe
                          du_seg'45'apply'45'mono_410 (coe du_seg'45'action_234 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken-cur
d_seg'45'weaken'45'cur_450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_292 -> T_AllSeg_292
d_seg'45'weaken'45'cur_450 ~v0 v1 v2 v3 v4 v5
  = du_seg'45'weaken'45'cur_450 v1 v2 v3 v4 v5
du_seg'45'weaken'45'cur_450 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_292 -> T_AllSeg_292
du_seg'45'weaken'45'cur_450 v0 v1 v2 v3 v4
  = coe
      du_seg'45'weaken_430 (coe C_mkSeg_224 (coe v0) (coe v2))
      (coe C_mkSeg_224 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_370 (coe v4) (coe du_saved'45'le'45'refl_374 (coe v2)))
-- Once.CCC.Codegen.SlotBudget.is-id?
d_is'45'id'63'_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegAction_226 -> Bool
d_is'45'id'63'_456 ~v0 v1 = du_is'45'id'63'_456 v1
du_is'45'id'63'_456 :: T_SegAction_226 -> Bool
du_is'45'id'63'_456 v0
  = case coe v0 of
      C_seg'45'id_228 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_230 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_232 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-idle?
d_seg'45'idle'63'_458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> Bool
d_seg'45'idle'63'_458 ~v0 v1 = du_seg'45'idle'63'_458 v1
du_seg'45'idle'63'_458 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> Bool
du_seg'45'idle'63'_458 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe du_is'45'id'63'_456 (coe du_seg'45'action_234 (coe v1)))
             (coe du_seg'45'idle'63'_458 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.idle-step
d_idle'45'step_468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_468 = erased
-- Once.CCC.Codegen.SlotBudget._.go
d_go_482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_214 ->
  T_SegAction_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_482 = erased
-- Once.CCC.Codegen.SlotBudget.idle-head
d_idle'45'head_488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_488 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-fst
d_'8743''45'fst_504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_504 = erased
-- Once.CCC.Codegen.SlotBudget.idle-tail
d_idle'45'tail_514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_514 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-snd
d_'8743''45'snd_530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_530 = erased
-- Once.CCC.Codegen.SlotBudget.idle-++
d_idle'45''43''43'_542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_542 = erased
-- Once.CCC.Codegen.SlotBudget.idle-neutral
d_idle'45'neutral_566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_566 = erased
-- Once.CCC.Codegen.SlotBudget.SegOK
d_SegOK_582 a0 a1 a2 = ()
newtype T_SegOK_582 = C_mkSegOK_604 ([Integer] -> T_AllSeg_292)
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-all
d_ok'45'all_598 :: T_SegOK_582 -> [Integer] -> T_AllSeg_292
d_ok'45'all_598 v0
  = case coe v0 of
      C_mkSegOK_604 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-neu
d_ok'45'neu_602 ::
  T_SegOK_582 ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_602 = erased
-- Once.CCC.Codegen.SlotBudget.segok-idle
d_segok'45'idle_610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_582
d_segok'45'idle_610 ~v0 ~v1 v2 ~v3 v4 = du_segok'45'idle_610 v2 v4
du_segok'45'idle_610 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_582
du_segok'45'idle_610 v0 v1
  = coe C_mkSegOK_604 (\ v2 -> coe du_go_626 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_292
d_go_626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 = du_go_626 v6 v8
du_go_626 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_292
du_go_626 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_296)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__304 v6 (coe du_go_626 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.segok-++
d_segok'45''43''43'_648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582 -> T_SegOK_582
d_segok'45''43''43'_648 ~v0 ~v1 v2 ~v3 v4 v5
  = du_segok'45''43''43'_648 v2 v4 v5
du_segok'45''43''43'_648 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582 -> T_SegOK_582
du_segok'45''43''43'_648 v0 v1 v2
  = coe
      C_mkSegOK_604
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_328 (coe v0) (coe d_ok'45'all_598 v1 v3)
           (coe d_ok'45'all_598 v2 v3))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 ->
  T_SegOK_582 ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_666 = erased
-- Once.CCC.Codegen.SlotBudget.segok-weaken
d_segok'45'weaken_676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_582 -> T_SegOK_582
d_segok'45'weaken_676 ~v0 v1 v2 v3 v4 v5
  = du_segok'45'weaken_676 v1 v2 v3 v4 v5
du_segok'45'weaken_676 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_582 -> T_SegOK_582
du_segok'45'weaken_676 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_604
      (\ v5 ->
         coe
           du_seg'45'weaken'45'cur_450 v0 v1 v5 v2 v3
           (coe d_ok'45'all_598 v4 v5))
-- Once.CCC.Codegen.SlotBudget.segok-pre
d_segok'45'pre_688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_582 -> T_SegOK_582
d_segok'45'pre_688 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_segok'45'pre_688 v2 v5 v6
du_segok'45'pre_688 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_582 -> T_SegOK_582
du_segok'45'pre_688 v0 v1 v2
  = coe
      du_segok'45''43''43'_648 (coe v0)
      (coe du_segok'45'idle_610 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotBudget.segok-thunk
d_segok'45'thunk_708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_segok'45'thunk_708 ~v0 v1 ~v2 ~v3 ~v4 v5 v6
  = du_segok'45'thunk_708 v1 v5 v6
du_segok'45'thunk_708 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
du_segok'45'thunk_708 v0 v1 v2
  = coe C_mkSegOK_604 (coe du_inner_728 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotBudget._.inner
d_inner_728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> [Integer] -> T_AllSeg_292
d_inner_728 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_inner_728 v1 v5 v6 v7
du_inner_728 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> [Integer] -> T_AllSeg_292
du_inner_728 v0 v1 v2 v3
  = coe
      C__'8759'__304 (coe du_sb'45'none_110)
      (coe
         du_allseg'45''43''43'_312 (coe v1)
         (coe
            d_ok'45'all_598 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__304 (coe du_sb'45'none_110)
            (coe C__'8759'__304 (coe du_sb'45'none_110) (coe C_'91''93'_296))))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_736 = erased
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_748 ~v0 v1 v2 ~v3 ~v4 = du_cata'45'mono_748 v1 v2
du_cata'45'mono_748 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_748 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v1)))
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
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v2))))
                      (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.frontier-mono
d_frontier'45'mono_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_786 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_786 (coe v0) (coe v1) (coe v7) (coe v10)
                (coe v4) (coe v5))
             (coe
                d_frontier'45'mono_786 (coe v0) (coe v7) (coe v2) (coe v9)
                (coe
                   du_budget'45'of_62
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
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
                                 d_frontier'45'mono_786 (coe v0) (coe v1) (coe v12) (coe v9)
                                 (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5))
                              (coe
                                 d_frontier'45'mono_786 (coe v0) (coe v1) (coe v13) (coe v10)
                                 (coe
                                    du_budget'45'of_62
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
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
                                 d_frontier'45'mono_786 (coe v0) (coe v1) (coe v12) (coe v9)
                                 (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                              (coe
                                 d_frontier'45'mono_786 (coe v0) (coe v1) (coe v13) (coe v10)
                                 (coe
                                    du_budget'45'of_62
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
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
                       d_frontier'45'mono_786 (coe v0) (coe v11) (coe v2) (coe v9)
                       (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5)))
                    (coe
                       d_frontier'45'mono_786 (coe v0) (coe v12) (coe v2) (coe v10)
                       (coe
                          du_budget'45'of_62
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                             (coe v0) (coe v11) (coe v2) (coe v4)
                             (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
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
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_frontier'45'mono_786 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                       (coe v2) (coe v9) (coe v4) (coe v5))
                    (coe
                       du_cata'45'mono_748
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v10)))
                       (coe
                          du_budget'45'of_62
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                             (coe v2) (coe v4) (coe v5) (coe v9))))
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
d_lt'45'refl_930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_930 ~v0 v1 = du_lt'45'refl_930 v1
du_lt'45'refl_930 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lt'45'refl_930 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_938 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'nat'45'layer'45'below_938 v4 v5
du_cata'45'nat'45'layer'45'below_938 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_938 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_110)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_144 (coe v0) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_144 (coe v1) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_144 (coe v0) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe v1) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-nat-below
d_cata'45'nat'45'below_964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_cata'45'nat'45'below_964 v0 v1 v2 v3 v4
  = coe
      du_segok'45'pre_688
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
      (coe
         du_segok'45''43''43'_648
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                     (coe
                        MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v2)))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                   (coe v2))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
         (coe
            du_segok'45'idle_610
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v2)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe v2))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (1 :: Integer)) (coe v2)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe du_descend_984))
         (coe
            du_segok'45'pre_688
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
            (coe
               du_segok'45''43''43'_648
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'nat'45'layer_64
                  (coe v1) (coe (0 :: Integer)))
               (coe
                  du_segok'45'idle_610
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'nat'45'layer_64
                     (coe v1) (coe (0 :: Integer)))
                  (coe du_layer_988 (coe v1)))
               (coe
                  du_segok'45'pre_688
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                  (coe
                     du_segok'45''43''43'_648 (coe v3)
                     (coe du_at''_982 (coe v1) (coe v3) (coe v4))
                     (coe
                        du_segok'45'pre_688
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (4 :: Integer)) (coe v2)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (5 :: Integer)) (coe v2)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_110)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                        (coe
                           du_segok'45''43''43'_648
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'nat'45'layer_64
                              (coe v1) (coe (1 :: Integer)))
                           (coe
                              du_segok'45'idle_610
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'nat'45'layer_64
                                 (coe v1) (coe (1 :: Integer)))
                              (coe du_layer_988 (coe v1)))
                           (coe
                              du_segok'45'pre_688
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_110)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                              (coe
                                 du_segok'45''43''43'_648 (coe v3)
                                 (coe du_at''_982 (coe v1) (coe v3) (coe v4))
                                 (coe
                                    du_segok'45'idle_610
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_86
                                       (coe v0) (coe v2))
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_110)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_978 ~v0 v1 ~v2 ~v3 ~v4 = du_p'60'b_978 v1
du_p'60'b_978 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_978 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_980 ~v0 v1 ~v2 ~v3 ~v4 = du_s'60'b_980 v1
du_s'60'b_980 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_980 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_at''_982 ~v0 v1 ~v2 v3 v4 = du_at''_982 v1 v3 v4
du_at''_982 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
du_at''_982 v0 v1 v2
  = coe
      du_segok'45'weaken_676 (coe v0)
      (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      (coe v2)
-- Once.CCC.Codegen.SlotBudget._.descend
d_descend_984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_descend_984 ~v0 ~v1 ~v2 ~v3 ~v4 = du_descend_984
du_descend_984 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_descend_984
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_110)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_110)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_110)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.layer
d_layer_988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_layer_988 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_layer_988 v1
du_layer_988 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_layer_988 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_110)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_144 (coe du_p'60'b_978 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_144 (coe du_s'60'b_980 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_144 (coe du_p'60'b_978 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe du_s'60'b_980 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-linear-below
d_cata'45'linear'45'below_1006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_cata'45'linear'45'below_1006 v0 v1 v2 v3 v4
  = coe
      du_segok'45''43''43'_648
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248
               (coe (0 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v2)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                       (coe addInt (coe (5 :: Integer)) (coe v1)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                   (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                         (coe addInt (coe (5 :: Integer)) (coe v1)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v1)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v1)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v1)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                           (coe
                                                                              addInt
                                                                              (coe (2 :: Integer))
                                                                              (coe v1)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                       (coe v0)
                                                                                       (coe v2))))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             addInt
                                                                                             (coe
                                                                                                (1 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v2)))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
      (coe
         du_segok'45'idle_610
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                     (coe addInt (coe (3 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v2)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (5 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe addInt (coe (2 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                      (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v1)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v1)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v1)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v1)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v1)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v2))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
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
                                                                                                   v2)))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
         (coe du_descend_1036 (coe v1)))
      (coe
         du_segok'45'pre_688
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
         (coe
            du_segok'45''43''43'_648 (coe v3)
            (coe du_at''_1034 (coe v1) (coe v3) (coe v4))
            (coe d_ascend_1056 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> Integer
d_b_1020 ~v0 v1 ~v2 ~v3 ~v4 = du_b_1020 v1
du_b_1020 :: Integer -> Integer
du_b_1020 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_1022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_1022 ~v0 v1 ~v2 ~v3 ~v4 = du_p0_1022 v1
du_p0_1022 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_1022 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_1024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_1024 ~v0 v1 ~v2 ~v3 ~v4 = du_p1_1024 v1
du_p1_1024 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_1024 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_1026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_1026 ~v0 v1 ~v2 ~v3 ~v4 = du_p2_1026 v1
du_p2_1026 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_1026 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_1028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_1028 ~v0 v1 ~v2 ~v3 ~v4 = du_p3_1028 v1
du_p3_1028 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_1028 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_1030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_1030 ~v0 v1 ~v2 ~v3 ~v4 = du_p4_1030 v1
du_p4_1030 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_1030 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_1032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_1032 ~v0 v1 ~v2 ~v3 ~v4 = du_p5_1032 v1
du_p5_1032 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_1032 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_1034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_at''_1034 ~v0 v1 ~v2 v3 v4 = du_at''_1034 v1 v3 v4
du_at''_1034 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
du_at''_1034 v0 v1 v2
  = coe
      du_segok'45'weaken_676 (coe v0) (coe du_b_1020 (coe v0)) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      (coe v2)
-- Once.CCC.Codegen.SlotBudget._.descend
d_descend_1036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_descend_1036 ~v0 v1 ~v2 ~v3 ~v4 = du_descend_1036 v1
du_descend_1036 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_descend_1036 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_110)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_144 (coe du_p3_1028 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe du_p5_1032 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_144 (coe du_p2_1026 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144 (coe du_p1_1024 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_144 (coe du_p5_1032 (coe v0))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_110)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_144
                                                            (coe du_p3_1028 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_110)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  du_sb'45'slot_144
                                                                  (coe du_p1_1024 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_144
                                                                     (coe du_p3_1028 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_144
                                                                        (coe du_p2_1026 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_110)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_110)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_110)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.ascend
d_ascend_1056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_ascend_1056 v0 v1 v2 v3 v4
  = coe
      du_segok'45'pre_688
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                  (coe addInt (coe (2 :: Integer)) (coe v2)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                     (coe addInt (coe (3 :: Integer)) (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                  (coe addInt (coe (4 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                     (coe addInt (coe (3 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                              (coe addInt (coe (5 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe addInt (coe (3 :: Integer)) (coe v1)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                (coe addInt (coe (5 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                      (coe addInt (coe (4 :: Integer)) (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                            (coe (2 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                               (coe v1))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248
                                                                     (coe (1 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v1)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                                 (coe v1))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_144 (coe du_p4_1030 (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_144 (coe du_p3_1028 (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_144 (coe du_p5_1032 (coe v1)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe du_p3_1028 (coe v1)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_144 (coe du_p1_1024 (coe v1)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144 (coe du_p5_1032 (coe v1)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_144 (coe du_p4_1030 (coe v1))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_110)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_110)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_144
                                                               (coe du_p0_1022 (coe v1)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_110)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_110)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_110)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_144
                                                                           (coe du_p1_1024 (coe v1))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_110)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'slot_144
                                                                                 (coe
                                                                                    du_p0_1022
                                                                                    (coe v1))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_110)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
      (coe
         du_segok'45''43''43'_648 (coe v3)
         (coe du_at''_1034 (coe v1) (coe v3) (coe v4))
         (coe
            du_segok'45'idle_610
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v2)))))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.push2-below
d_push2'45'below_1086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_1086 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_push2'45'below_1086 v5 v6 v7
du_push2'45'below_1086 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_1086 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_144 (coe v1) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_144 (coe v2) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_144 (coe v1) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_144 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_144 (coe v2) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe v0) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.pop2-below
d_pop2'45'below_1118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_1118 ~v0 ~v1 ~v2 v3 = du_pop2'45'below_1118 v3
du_pop2'45'below_1118 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_1118 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_144 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_144 (coe v0) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.SlotBudget.wrap-sum-below
d_wrap'45'sum'45'below_1136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_1136 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_wrap'45'sum'45'below_1136 v4 v5
du_wrap'45'sum'45'below_1136 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_1136 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_144 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_144 (coe v1) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_144 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_144 (coe v1) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
-- Once.CCC.Codegen.SlotBudget.visit-below
d_visit'45'below_1170 ::
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
d_visit'45'below_1170 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_visit'45'below_1170 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_visit'45'below_1170 ::
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
du_visit'45'below_1170 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_114 v11
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_110)
             (coe du_push2'45'below_1086 (coe v7) (coe v8) (coe v9))
      MAlonzo.Code.Once.Type.C__'8853'__118 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_110)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_110)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_182
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v11)))
                      (coe v6)))
                (coe
                   du_visit'45'below_1170 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v11)))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1244 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_110)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_110)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_110)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_182
                         (coe v0) (coe v2) (coe v3) (coe v4) (coe v11)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         du_visit'45'below_1170 (coe v0) (coe v11) (coe v2) (coe v3)
                         (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v7) (coe v8)
                         (coe v9) (coe du_recF_1240 (coe v11) (coe v12) (coe v5) (coe v10)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v11 v12
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_144
                      (coe du_s'60'b_1280 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_110)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_182
                   (coe v0) (coe v2) (coe v3) (coe v4) (coe v12)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v11))
                      (coe v6)))
                (coe
                   du_visit'45'below_1170 (coe v0) (coe v12) (coe v2) (coe v3)
                   (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v11))
                      (coe v6))
                   (coe v7) (coe v8) (coe v9)
                   (coe du_recG_1288 (coe v11) (coe v12) (coe v5) (coe v10)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_144
                         (coe du_s'60'b_1280 (coe v11) (coe v12) (coe v5) (coe v10)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_110)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_1170 (coe v0) (coe v11) (coe v2) (coe v3)
                      (coe v4) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe du_recF_1284 (coe v11) (coe v12) (coe v5) (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1240 ::
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
d_recF_1240 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1240 v1 v2 v6 v12
du_recF_1240 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1240 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1244 ::
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
d_recG_1244 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1244 v1 v2 v6 v12
du_recG_1244 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1244 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1276 ::
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
d_room4_1276 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_room4_1276 v1 v2 v6 v12
du_room4_1276 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1276 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1280 ::
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
d_s'60'b_1280 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_s'60'b_1280 v1 v2 v6 v12
du_s'60'b_1280 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1280 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1276 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1284 ::
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
d_recF_1284 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recF_1284 v1 v2 v6 v12
du_recF_1284 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1284 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1288 ::
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
d_recG_1288 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_recG_1288 v1 v2 v6 v12
du_recG_1288 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1288 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.rebuild-below
d_rebuild'45'below_1310 ::
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
d_rebuild'45'below_1310 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_rebuild'45'below_1310 v0 v1 v2 v5 v6 v8 v9
du_rebuild'45'below_1310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_1310 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_114 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_110)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe du_pop2'45'below_1118 (coe v5)
      MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_110)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_110)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
                   (coe v0) (coe v2) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v7)))
                      (coe v4)))
                (coe
                   du_rebuild'45'below_1310 (coe v0) (coe v8) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v7)))
                      (coe v4))
                   (coe v5) (coe du_recG_1384 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_156
                      (coe (1 :: Integer)) (coe v3))
                   (coe
                      du_wrap'45'sum'45'below_1136
                      (coe du_s'60'b_1372 (coe v7) (coe v8) (coe v3) (coe v6))
                      (coe du_b'45'ss_1376 (coe v7) (coe v8) (coe v3) (coe v6)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_110)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_110)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_110)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
                            (coe v0) (coe v2) (coe v7)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            du_rebuild'45'below_1310 (coe v0) (coe v7) (coe v2)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5)
                            (coe du_recF_1380 (coe v7) (coe v8) (coe v3) (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_156
                               (coe (0 :: Integer)) (coe v3))
                            (coe
                               du_wrap'45'sum'45'below_1136
                               (coe du_s'60'b_1372 (coe v7) (coe v8) (coe v3) (coe v6))
                               (coe du_b'45'ss_1376 (coe v7) (coe v8) (coe v3) (coe v6)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_110)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_144
                      (coe du_s'60'b_1416 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_110)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_110)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
                   (coe v0) (coe v2) (coe v7)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                (coe
                   du_rebuild'45'below_1310 (coe v0) (coe v7) (coe v2)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe du_recF_1436 (coe v7) (coe v8) (coe v3) (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe
                         du_sb'45'slot_144
                         (coe du_b'45'ss_1420 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_144
                            (coe du_s'60'b_1416 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_110)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_110)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
                         (coe v0) (coe v2) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v7))
                            (coe v4)))
                      (coe
                         du_rebuild'45'below_1310 (coe v0) (coe v8) (coe v2)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162 (coe v7))
                            (coe v4))
                         (coe v5) (coe du_recG_1440 (coe v7) (coe v8) (coe v3) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_144
                            (coe du_b'45's2_1424 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_110)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  du_sb'45'slot_144
                                  (coe du_b'45's3_1430 (coe v7) (coe v8) (coe v3) (coe v6)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_110)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        du_sb'45'slot_144
                                        (coe du_b'45'ss_1420 (coe v7) (coe v8) (coe v3) (coe v6))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe du_sb'45'none_110)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              du_sb'45'slot_144
                                              (coe
                                                 du_b'45's2_1424 (coe v7) (coe v8) (coe v3)
                                                 (coe v6))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe du_sb'45'none_110)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe
                                                    du_sb'45'slot_144
                                                    (coe
                                                       du_b'45's3_1430 (coe v7) (coe v8) (coe v3)
                                                       (coe v6))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1368 ::
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
d_room4_1368 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1368 v1 v2 v6 v10
du_room4_1368 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1368 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1372 ::
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
d_s'60'b_1372 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1372 v1 v2 v6 v10
du_s'60'b_1372 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1372 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1368 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1376 ::
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
d_b'45'ss_1376 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1376 v1 v2 v6 v10
du_b'45'ss_1376 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1376 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1368 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1380 ::
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
d_recF_1380 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1380 v1 v2 v6 v10
du_recF_1380 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1380 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1384 ::
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
d_recG_1384 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1384 v1 v2 v6 v10
du_recG_1384 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1384 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room4_1412 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_room4_1412 v1 v2 v6 v10
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_1416 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_s'60'b_1416 v1 v2 v6 v10
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
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1420 ::
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
d_b'45'ss_1420 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45'ss_1420 v1 v2 v6 v10
du_b'45'ss_1420 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1420 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1412 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_1424 ::
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
d_b'45's2_1424 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's2_1424 v1 v2 v6 v10
du_b'45's2_1424 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_1424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_1412 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_1430 ::
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
d_b'45's3_1430 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_b'45's3_1430 v1 v2 v6 v10
du_b'45's3_1430 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_1430 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_1412 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1436 ::
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
d_recF_1436 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recF_1436 v1 v2 v6 v10
du_recF_1436 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1436 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1440 ::
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
d_recG_1440 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_recG_1440 v1 v2 v6 v10
du_recG_1440 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1440 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))))
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
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.visit-idle
d_visit'45'idle_1472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_1472 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1534 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1592 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_cata'45'branching'45'below_1592 v0 v1 v2 v3 v4 v5
  = coe
      du_segok'45''43''43'_648
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_292
         (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         du_segok'45'idle_610
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_292
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_I'8321''45'all_1646 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         du_segok'45''43''43'_648 (coe v4)
         (coe du_at''_1642 (coe v1) (coe v2) (coe v4) (coe v5))
         (coe
            du_segok'45'idle_610
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_300
               (coe v0) (coe v2) (coe v3))
            (coe du_I'8322''45'all_1680 (coe v1) (coe v2))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> Integer
d_b_1608 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_b_1608 v1 v2
du_b_1608 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> Integer -> Integer
du_b_1608 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1610 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_fixed7_1610 v1 v2
du_fixed7_1610 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1610 v0 v1
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
            (coe v1)))
-- Once.CCC.Codegen.SlotBudget._.fixed7'
d_fixed7''_1612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1612 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_fixed7''_1612 v1 v2
du_fixed7''_1612 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1612 v0 v1 = coe du_fixed7_1610 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1616 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q0_1616 v1 v2
du_q0_1616 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1616 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1618 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q1_1618 v1 v2
du_q1_1618 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1618 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1620 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q2_1620 v1 v2
du_q2_1620 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1620 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1624 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q3_1624 v1 v2
du_q3_1624 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1624 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1628 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1628 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q4_1628 v1 v2
du_q4_1628 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1628 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1632 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q5_1632 v1 v2
du_q5_1632 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1632 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1636 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_q6_1636 v1 v2
du_q6_1636 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1636 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1612 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1640 ~v0 v1 v2 ~v3 ~v4 ~v5
  = du_walk'45'room_1640 v1 v2
du_walk'45'room_1640 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1640 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe
         addInt
         (coe
            addInt (coe (7 :: Integer))
            (coe
               mulInt (coe (4 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_122 (coe v0))))
         (coe v1))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_1642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_at''_1642 ~v0 v1 v2 ~v3 v4 v5 = du_at''_1642 v1 v2 v4 v5
du_at''_1642 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
du_at''_1642 v0 v1 v2 v3
  = coe
      du_segok'45'weaken_676 (coe v1) (coe du_b_1608 (coe v0) (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v1))
         (coe du_fixed7_1610 (coe v0) (coe v1)))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.I₁-idle
d_I'8321''45'idle_1644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1644 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1646 v0 v1 v2 v3 ~v4 ~v5
  = du_I'8321''45'all_1646 v0 v1 v2 v3
du_I'8321''45'all_1646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1646 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_144 (coe du_q3_1624 (coe v1) (coe v2)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_144 (coe du_q6_1636 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_144 (coe du_q6_1636 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe du_q1_1618 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_144 (coe du_q6_1636 (coe v1) (coe v2)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144 (coe du_q2_1620 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144 (coe du_q6_1636 (coe v1) (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144 (coe du_q0_1616 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_144
                                                   (coe du_q3_1624 (coe v1) (coe v2)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_138 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            du_push2'45'below_1086 (coe du_q0_1616 (coe v1) (coe v2))
            (coe du_q4_1628 (coe v1) (coe v2))
            (coe du_q5_1632 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_110)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_144 (coe du_q0_1616 (coe v1) (coe v2)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_144 (coe du_q0_1616 (coe v1) (coe v2)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_110)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144 (coe du_q3_1624 (coe v1) (coe v2))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144 (coe du_q3_1624 (coe v1) (coe v2))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_138
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  du_push2'45'below_1086 (coe du_q1_1618 (coe v1) (coe v2))
                  (coe du_q4_1628 (coe v1) (coe v2))
                  (coe du_q5_1632 (coe v1) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_144 (coe du_q3_1624 (coe v1) (coe v2)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_110)
                        (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_182
                        (coe v0) (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        du_visit'45'below_1170 (coe v0) (coe v1) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3))
                        (coe du_q0_1616 (coe v1) (coe v2))
                        (coe du_q4_1628 (coe v1) (coe v2))
                        (coe du_q5_1632 (coe v1) (coe v2))
                        (coe du_walk'45'room_1640 (coe v1) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_110)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_144 (coe du_q1_1618 (coe v1) (coe v2)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_110)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144 (coe du_q1_1618 (coe v1) (coe v2))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_110)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_242
                                 (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162
                                          (coe v1)))
                                    (coe v3)))
                              (coe
                                 du_rebuild'45'below_1310 (coe v0) (coe v1)
                                 (coe addInt (coe (2 :: Integer)) (coe v2))
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_162
                                          (coe v1)))
                                    (coe v3))
                                 (coe du_q2_1620 (coe v1) (coe v2))
                                 (coe du_walk'45'room_1640 (coe v1) (coe v2)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_110)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1680 ~v0 v1 v2 ~v3 ~v4 ~v5
  = du_I'8322''45'all_1680 v1 v2
du_I'8322''45'all_1680 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1680 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_138
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_1086 (coe du_q2_1620 (coe v0) (coe v1))
         (coe du_q4_1628 (coe v0) (coe v1))
         (coe du_q5_1632 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_110)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_110)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_144 (coe du_q2_1620 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_110)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_110)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_582 -> T_SegOK_582
d_cata'45'slots'45'below_1692 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe v5
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             d_cata'45'nat'45'below_964 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             d_cata'45'linear'45'below_1006 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v6
        -> coe
             d_cata'45'branching'45'below_1592 (coe v0) (coe v6) (coe v2)
             (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_1738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer -> T_SegOK_582
d_slots'45'below_1738 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v1) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             du_segok'45''43''43'_648
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                du_segok'45'weaken_676
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   du_budget'45'of_62
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10)))
                (coe
                   du_trace'45'of_66
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                      (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                (coe
                   d_frontier'45'mono_786 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))))
                (coe
                   d_slots'45'below_1738 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                   (coe v5)))
             (coe
                du_segok'45'pre_688
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_110)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_1738 (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                         (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                            (coe v0) (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_688
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v4))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          d_h_1780 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                          (coe v10) (coe v4) (coe v5)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_648
                              (coe
                                 du_trace'45'of_66
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_segok'45'weaken_676
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    du_budget'45'of_62
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
                                          v11)))
                                 (coe
                                    du_trace'45'of_66
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    d_frontier'45'mono_786 (coe v0) (coe v1) (coe v13) (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))))
                                 (coe
                                    d_slots'45'below_1738 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)))
                              (coe
                                 du_segok'45'pre_688
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                                          (coe v4))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_144
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             d_h_1780 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                             (coe v10) (coe v4) (coe v5)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                d_h_1780 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_648
                                    (coe
                                       du_trace'45'of_66
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0) (coe v1) (coe v13)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                   (coe v0) (coe v1) (coe v12)
                                                   (coe addInt (coe (3 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9))))
                                          (coe v10)))
                                    (coe
                                       d_slots'45'below_1738 (coe v0) (coe v1) (coe v13) (coe v10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))))
                                    (coe
                                       du_segok'45'idle_610
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144
                                             (coe
                                                d_h_1780 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   (coe
                                                      d_h_1780 (coe v0) (coe v1) (coe v12) (coe v13)
                                                      (coe v9) (coe v10) (coe v4) (coe v5)))
                                                (coe
                                                   (\ v14 v15 ->
                                                      d_h_1780
                                                        (coe v0) (coe v1) (coe v12) (coe v13)
                                                        (coe v9) (coe v10) (coe v4) (coe v5))))
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_688
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v4))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          d_h_1804 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                          (coe v10) (coe v4) (coe v5)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_648
                              (coe
                                 du_trace'45'of_66
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                    (coe v0) (coe v1) (coe v12)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v9)))
                              (coe
                                 du_segok'45'weaken_676
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    du_budget'45'of_62
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
                                          v11)))
                                 (coe
                                    du_trace'45'of_66
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                       (coe v0) (coe v1) (coe v12)
                                       (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                       (coe v9)))
                                 (coe
                                    d_frontier'45'mono_786 (coe v0) (coe v1) (coe v13) (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0) (coe v1) (coe v12)
                                          (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                          (coe v9)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))))
                                 (coe
                                    d_slots'45'below_1738 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)))
                              (coe
                                 du_segok'45'pre_688
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                                          (coe v4))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_144
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             d_h_1804 (coe v0) (coe v1) (coe v12) (coe v13) (coe v9)
                                             (coe v10) (coe v4) (coe v5)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                d_h_1804 (coe v0) (coe v1) (coe v12) (coe v13)
                                                (coe v9) (coe v10) (coe v4) (coe v5)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_648
                                    (coe
                                       du_trace'45'of_66
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0) (coe v1) (coe v13)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                   (coe v0) (coe v1) (coe v12)
                                                   (coe addInt (coe (4 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9))))
                                          (coe v10)))
                                    (coe
                                       d_slots'45'below_1738 (coe v0) (coe v1) (coe v13) (coe v10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                             (coe v0) (coe v1) (coe v12)
                                             (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                             (coe v9)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                                (coe v0) (coe v1) (coe v12)
                                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5)
                                                (coe v9)))))
                                    (coe
                                       du_segok'45'idle_610
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                   (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v4)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                (coe
                                                   d_h_1804 (coe v0) (coe v1) (coe v12) (coe v13)
                                                   (coe v9) (coe v10) (coe v4) (coe v5)))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_144
                                                   (coe
                                                      d_h_1804 (coe v0) (coe v1) (coe v12) (coe v13)
                                                      (coe v9) (coe v10) (coe v4) (coe v5))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_110)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_144
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            (coe
                                                               d_h_1804 (coe v0) (coe v1) (coe v12)
                                                               (coe v13) (coe v9) (coe v10) (coe v4)
                                                               (coe v5)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_110)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_144
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                  (coe
                                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v4)))
                                                                  (coe
                                                                     d_h_1804 (coe v0) (coe v1)
                                                                     (coe v12) (coe v13) (coe v9)
                                                                     (coe v10) (coe v4) (coe v5)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_110)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_144
                                                                     (coe
                                                                        d_h_1804 (coe v0) (coe v1)
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
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v9))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_fst_44)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_snd_50)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_610
                           (coe
                              du_trace'45'of_66
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144
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
                           du_segok'45'idle_610
                           (coe
                              du_trace'45'of_66
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_144
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_110)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_144
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
                           du_segok'45'idle_610
                           (coe
                              du_trace'45'of_66
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144
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
                           du_segok'45'idle_610
                           (coe
                              du_trace'45'of_66
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                 (coe v0) (coe v1)
                                 (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_144
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_110)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_144
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
                    du_segok'45'pre_688
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe du_sb'45'none_110)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_110)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       du_segok'45''43''43'_648
                       (coe
                          du_trace'45'of_66
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                             (coe v0) (coe v12) (coe v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                             (coe v10)))
                       (coe
                          d_slots'45'below_1738 (coe v0) (coe v12) (coe v2) (coe v10)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                (coe v0) (coe v11) (coe v2) (coe v4)
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                       (coe
                          du_segok'45'pre_688
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_110)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe du_sb'45'none_110)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_110)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe du_sb'45'none_110)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                          (coe
                             du_segok'45''43''43'_648
                             (coe
                                du_trace'45'of_66
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                   (coe v0) (coe v11) (coe v2) (coe v4)
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                             (coe
                                du_segok'45'weaken_676
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   du_budget'45'of_62
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                      (coe MAlonzo.Code.Once.IR.C_case_70 v9 v10)))
                                (coe
                                   du_trace'45'of_66
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                      (coe v0) (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   d_frontier'45'mono_786 (coe v0) (coe v12) (coe v2) (coe v10)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                         (coe v0) (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                            (coe v0) (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                                (coe
                                   d_slots'45'below_1738 (coe v0) (coe v11) (coe v2) (coe v9)
                                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v5))))
                             (coe
                                du_segok'45'idle_610
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_110)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_terminal_74)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v2) (coe v4)
                   (coe v5) (coe MAlonzo.Code.Once.IR.C_initial_78)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_688
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v5)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210
                                             (coe v4))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_144
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                (\ v13 v14 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v13)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                           (coe
                              du_segok'45'thunk_708
                              (coe
                                 du_budget'45'of_62
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                    (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                          (coe v12) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                              (coe
                                 d_slots'45'below_1738 (coe v0)
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                 (coe v12) (coe v9) (coe (0 :: Integer))
                                 (coe addInt (coe (2 :: Integer)) (coe v5))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_688
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                (coe v4))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0) (coe v5)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v4)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
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
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_144
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_144
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_110)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_110)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_110)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_144
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v4)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_110)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
                           (coe
                              du_segok'45'thunk_708
                              (coe
                                 du_budget'45'of_62
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                    (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v9 v10)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                          (coe v12) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                              (coe
                                 d_slots'45'below_1738 (coe v0)
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
                           du_segok'45'idle_610
                           (coe
                              du_trace'45'of_66
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v10) (coe v2))
                                    (coe v10))
                                 (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_110)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_144
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_110)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_110)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_110)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_110)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_144
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_110)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_144
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v4)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_110)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_144
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v4)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_110)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_144
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v4)))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_110)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_144
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
                                                                           (coe du_sb'45'none_110)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'none_110)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    d_cata'45'slots'45'below_1692 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                             (coe v2) (coe v4) (coe v5) (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                                (coe v2) (coe v4) (coe v5) (coe v9)))))
                    (coe
                       d_slots'45'below_1738 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                       (coe v2) (coe v9) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v7 v9
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Para_112 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Out_116 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_Out_116 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8)))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_126 v7 v9
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_126 v7 v9)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v6
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4) (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_const_148 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    du_segok'45'idle_610
                    (coe
                       du_trace'45'of_66
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_110)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
        -> coe
             du_segok'45'idle_610
             (coe
                du_trace'45'of_66
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7)) (coe v4)
                   (coe v5) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_110)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1780 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_786 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_786 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_62
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (3 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1804 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_786 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
      (coe
         d_frontier'45'mono_786 (coe v0) (coe v1) (coe v3) (coe v5)
         (coe
            du_budget'45'of_62
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
               (coe v0) (coe v1) (coe v2)
               (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
                  (coe v0) (coe v1) (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7) (coe v4)))))
-- Once.CCC.Codegen.SlotBudget.trace-lookup
d_trace'45'lookup_1972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_trace'45'lookup_1972 ~v0 v1 v2 = du_trace'45'lookup_1972 v1 v2
du_trace'45'lookup_1972 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_trace'45'lookup_1972 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_trace'45'lookup_1972 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.fetch-at
d_fetch'45'at_1980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch'45'at_1980 ~v0 = du_fetch'45'at_1980
du_fetch'45'at_1980 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch'45'at_1980 = coe du_trace'45'lookup_1972
-- Once.CCC.Codegen.SlotBudget.seg-at
d_seg'45'at_1982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_SegState_214 -> T_SegState_214
d_seg'45'at_1982 ~v0 v1 v2 v3 = du_seg'45'at_1982 v1 v2 v3
du_seg'45'at_1982 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_SegState_214 -> T_SegState_214
du_seg'45'at_1982 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       du_seg'45'at_1982 (coe v5) (coe v3)
                       (coe du_seg'45'step_256 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotBudget.seg-at-suc
d_seg'45'at'45'suc_2004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegState_214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_2004 = erased
-- Once.CCC.Codegen.SlotBudget.idle-seg-at
d_idle'45'seg'45'at_2032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_2032 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_2066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  T_SegState_214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_2066 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_2102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  T_SegState_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_2102 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ˡ
d_fetch'45''43''43''737'_2126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_2126 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ʳ
d_fetch'45''43''43''691'_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_2154 = erased
-- Once.CCC.Codegen.SlotBudget.split-pos
d_split'45'pos_2174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_2174 ~v0 v1 v2 = du_split'45'pos_2174 v1 v2
du_split'45'pos_2174 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split'45'pos_2174 v0 v1
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
                    (let v5 = coe du_split'45'pos_2174 (coe v3) (coe v4) in
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
d_allseg'45'at_2218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_SegState_214 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_AllSeg_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_82
d_allseg'45'at_2218 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_allseg'45'at_2218 v2 v3 v5
du_allseg'45'at_2218 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_AllSeg_292 -> T_SlotBelow_82
du_allseg'45'at_2218 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__304 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__304 v9 v10
                         -> coe du_allseg'45'at_2218 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-seg
d_ir'45'slots'45'below'45'seg_2248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_SegOK_582
d_ir'45'slots'45'below'45'seg_2248 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_348
              (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
              (coe (0 :: Integer)) (coe v3) in
    coe
      (let v5
             = d_slots'45'below_1738
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
d_emitted'45'slot'45'seg_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_2272 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_emitted'45'slot'45'seg_2272 v0 v1 v2 v3 v4 v6
du_emitted'45'slot'45'seg_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_2272 v0 v1 v2 v3 v4 v5
  = coe
      d_below_98
      (coe
         du_allseg'45'at_2218
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4)
         (coe
            d_ok'45'all_598
            (d_ir'45'slots'45'below'45'seg_2248
               (coe v0) (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      v5 erased
