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
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.SlotBudget.budget-of
d_budget'45'of_8 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.trace-of
d_trace'45'of_12 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_trace'45'of_12 v0
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
d_cata'45'budget'45'of_16 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_cata'45'budget'45'of_16 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.cata-trace-of
d_cata'45'trace'45'of_20 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_cata'45'trace'45'of_20 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow
d_SlotBelow_28 a0 a1 = ()
data T_SlotBelow_28
  = C_mkSlotBelow_50 (Integer ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                     (Integer ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.SlotBudget.SlotBelow.below
d_below_44 ::
  T_SlotBelow_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_44 v0
  = case coe v0 of
      C_mkSlotBelow_50 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SlotBelow.pair-below
d_pair'45'below_48 ::
  T_SlotBelow_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pair'45'below_48 v0
  = case coe v0 of
      C_mkSlotBelow_50 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-none
d_sb'45'none_56 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_28
d_sb'45'none_56 ~v0 ~v1 ~v2 = du_sb'45'none_56
du_sb'45'none_56 :: T_SlotBelow_28
du_sb'45'none_56
  = coe
      C_mkSlotBelow_50 (coe (\ v0 v1 -> coe du_go_72))
      (coe (\ v0 v1 -> coe du_go_72))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_72 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_go_72
du_go_72 :: AgdaAny
du_go_72 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-slot
d_sb'45'slot_90 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_28
d_sb'45'slot_90 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sb'45'slot_90 v4 v5
du_sb'45'slot_90 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_28
du_sb'45'slot_90 v0 v1
  = coe C_mkSlotBelow_50 (coe (\ v2 v3 -> v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.just-inj
d_just'45'inj_108 ::
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
d_just'45'inj_108 = erased
-- Once.CCC.Codegen.SlotBudget.sb-weaken
d_sb'45'weaken_122 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_122 ~v0 ~v1 v2 v3 v4 = du_sb'45'weaken_122 v2 v3 v4
du_sb'45'weaken_122 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sb'45'weaken_122 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       C_mkSlotBelow_50
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_below_44 v5 v9 erased) (coe v1)))
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_pair'45'below_48 v5 v9 erased) (coe v1))))
                    (coe du_sb'45'weaken_122 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.sb-le
d_sb'45'le_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_28 -> T_SlotBelow_28
d_sb'45'le_146 ~v0 ~v1 ~v2 v3 v4 = du_sb'45'le_146 v3 v4
du_sb'45'le_146 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_28 -> T_SlotBelow_28
du_sb'45'le_146 v0 v1
  = coe
      C_mkSlotBelow_50
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_below_44 v1 v2 erased) (coe v0)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_pair'45'below_48 v1 v2 erased) (coe v0)))
-- Once.CCC.Codegen.SlotBudget.SegState
d_SegState_160 = ()
data T_SegState_160 = C_mkSeg_170 Integer [Integer]
-- Once.CCC.Codegen.SlotBudget.SegState.cur
d_cur_166 :: T_SegState_160 -> Integer
d_cur_166 v0
  = case coe v0 of
      C_mkSeg_170 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegState.saved
d_saved_168 :: T_SegState_160 -> [Integer]
d_saved_168 v0
  = case coe v0 of
      C_mkSeg_170 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegAction
d_SegAction_172 = ()
data T_SegAction_172
  = C_seg'45'id_174 | C_seg'45'push_176 Integer | C_seg'45'pop_178
-- Once.CCC.Codegen.SlotBudget.seg-action
d_seg'45'action_180 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegAction_172
d_seg'45'action_180 v0
  = let v1 = coe C_seg'45'id_174 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v3 v4
                  -> coe C_seg'45'push_176 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v3
                  -> coe C_seg'45'pop_178
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotBudget.pop-with
d_pop'45'with_184 :: [Integer] -> T_SegState_160 -> T_SegState_160
d_pop'45'with_184 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_170 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply
d_seg'45'apply_192 ::
  T_SegAction_172 -> T_SegState_160 -> T_SegState_160
d_seg'45'apply_192 v0 v1
  = case coe v0 of
      C_seg'45'id_174 -> coe v1
      C_seg'45'push_176 v2
        -> coe
             C_mkSeg_170 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_166 (coe v1)) (coe d_saved_168 (coe v1)))
      C_seg'45'pop_178
        -> coe d_pop'45'with_184 (coe d_saved_168 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-step
d_seg'45'step_202 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegState_160 -> T_SegState_160
d_seg'45'step_202 v0 v1
  = coe
      d_seg'45'apply_192 (coe d_seg'45'action_180 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotBudget.seg-fold
d_seg'45'fold_208 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegState_160 -> T_SegState_160
d_seg'45'fold_208 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_seg'45'fold_208 (coe v3)
             (coe d_seg'45'step_202 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-fold-++
d_seg'45'fold'45''43''43'_224 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_224 = erased
-- Once.CCC.Codegen.SlotBudget.AllSeg
d_AllSeg_238 a0 a1 = ()
data T_AllSeg_238
  = C_'91''93'_242 | C__'8759'__250 T_SlotBelow_28 T_AllSeg_238
-- Once.CCC.Codegen.SlotBudget.allseg-++
d_allseg'45''43''43'_258 ::
  T_SegState_160 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_238 -> T_AllSeg_238 -> T_AllSeg_238
d_allseg'45''43''43'_258 ~v0 v1 ~v2 v3 v4
  = du_allseg'45''43''43'_258 v1 v3 v4
du_allseg'45''43''43'_258 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_238 -> T_AllSeg_238 -> T_AllSeg_238
du_allseg'45''43''43'_258 v0 v1 v2
  = case coe v1 of
      C_'91''93'_242 -> coe v2
      C__'8759'__250 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__250 v6
                    (coe du_allseg'45''43''43'_258 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.allseg-++bal
d_allseg'45''43''43'bal_274 ::
  T_SegState_160 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_238 -> T_AllSeg_238 -> T_AllSeg_238
d_allseg'45''43''43'bal_274 ~v0 v1 ~v2 ~v3 v4 v5
  = du_allseg'45''43''43'bal_274 v1 v4 v5
du_allseg'45''43''43'bal_274 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_AllSeg_238 -> T_AllSeg_238 -> T_AllSeg_238
du_allseg'45''43''43'bal_274 v0 v1 v2
  = coe du_allseg'45''43''43'_258 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotBudget.SavedLE
d_SavedLE_284 a0 a1 = ()
data T_SavedLE_284
  = C_'91''93'_286 |
    C__'8759'__296 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_284
-- Once.CCC.Codegen.SlotBudget.SegLE
d_SegLE_302 a0 a1 = ()
data T_SegLE_302
  = C_mkSegLE_316 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_284
-- Once.CCC.Codegen.SlotBudget.SegLE.cur-le
d_cur'45'le_312 ::
  T_SegLE_302 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_312 v0
  = case coe v0 of
      C_mkSegLE_316 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegLE.saved-le
d_saved'45'le_314 :: T_SegLE_302 -> T_SavedLE_284
d_saved'45'le_314 v0
  = case coe v0 of
      C_mkSegLE_316 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.saved-le-refl
d_saved'45'le'45'refl_320 :: [Integer] -> T_SavedLE_284
d_saved'45'le'45'refl_320 v0
  = case coe v0 of
      [] -> coe C_'91''93'_286
      (:) v1 v2
        -> coe
             C__'8759'__296
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (d_saved'45'le'45'refl_320 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.pop-mono
d_pop'45'mono_334 ::
  T_SegState_160 ->
  T_SegState_160 ->
  [Integer] ->
  [Integer] -> T_SavedLE_284 -> T_SegLE_302 -> T_SegLE_302
d_pop'45'mono_334 ~v0 ~v1 v2 v3 v4 v5
  = du_pop'45'mono_334 v2 v3 v4 v5
du_pop'45'mono_334 ::
  [Integer] ->
  [Integer] -> T_SavedLE_284 -> T_SegLE_302 -> T_SegLE_302
du_pop'45'mono_334 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__296 v10 v11 -> coe C_mkSegLE_316 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-apply-mono
d_seg'45'apply'45'mono_356 ::
  T_SegAction_172 ->
  T_SegState_160 -> T_SegState_160 -> T_SegLE_302 -> T_SegLE_302
d_seg'45'apply'45'mono_356 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_174 -> coe v3
      C_seg'45'push_176 v4
        -> coe
             C_mkSegLE_316
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_166 (coe d_seg'45'apply_192 (coe v0) (coe v1))))
             (coe
                C__'8759'__296 (d_cur'45'le_312 (coe v3))
                (d_saved'45'le_314 (coe v3)))
      C_seg'45'pop_178
        -> coe
             du_pop'45'mono_334 (coe d_saved_168 (coe v1))
             (coe d_saved_168 (coe v2)) (coe d_saved'45'le_314 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken
d_seg'45'weaken_376 ::
  T_SegState_160 ->
  T_SegState_160 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegLE_302 -> T_AllSeg_238 -> T_AllSeg_238
d_seg'45'weaken_376 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_242 -> coe C_'91''93'_242
      C__'8759'__250 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__250
                    (coe du_sb'45'le_146 (coe d_cur'45'le_312 (coe v3)) (coe v8))
                    (d_seg'45'weaken_376
                       (coe
                          d_seg'45'apply_192 (coe d_seg'45'action_180 (coe v10)) (coe v0))
                       (coe d_seg'45'step_202 (coe v10) (coe v1)) (coe v11)
                       (coe
                          d_seg'45'apply'45'mono_356 (coe d_seg'45'action_180 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-weaken-cur
d_seg'45'weaken'45'cur_396 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_238 -> T_AllSeg_238
d_seg'45'weaken'45'cur_396 v0 v1 v2 v3 v4
  = coe
      d_seg'45'weaken_376 (coe C_mkSeg_170 (coe v0) (coe v2))
      (coe C_mkSeg_170 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_316 (coe v4) (coe d_saved'45'le'45'refl_320 (coe v2)))
-- Once.CCC.Codegen.SlotBudget.is-id?
d_is'45'id'63'_402 :: T_SegAction_172 -> Bool
d_is'45'id'63'_402 v0
  = case coe v0 of
      C_seg'45'id_174 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_176 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_178 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.seg-idle?
d_seg'45'idle'63'_404 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> Bool
d_seg'45'idle'63'_404 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is'45'id'63'_402 (coe d_seg'45'action_180 (coe v1)))
             (coe d_seg'45'idle'63'_404 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.idle-step
d_idle'45'step_414 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_414 = erased
-- Once.CCC.Codegen.SlotBudget._.go
d_go_428 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_160 ->
  T_SegAction_172 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_428 = erased
-- Once.CCC.Codegen.SlotBudget.idle-head
d_idle'45'head_434 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_434 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-fst
d_'8743''45'fst_450 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_450 = erased
-- Once.CCC.Codegen.SlotBudget.idle-tail
d_idle'45'tail_460 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_460 = erased
-- Once.CCC.Codegen.SlotBudget._.∧-snd
d_'8743''45'snd_476 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_476 = erased
-- Once.CCC.Codegen.SlotBudget.idle-++
d_idle'45''43''43'_488 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_488 = erased
-- Once.CCC.Codegen.SlotBudget.idle-neutral
d_idle'45'neutral_512 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_512 = erased
-- Once.CCC.Codegen.SlotBudget.SegOK
d_SegOK_528 a0 a1 = ()
newtype T_SegOK_528 = C_mkSegOK_550 ([Integer] -> T_AllSeg_238)
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-all
d_ok'45'all_544 :: T_SegOK_528 -> [Integer] -> T_AllSeg_238
d_ok'45'all_544 v0
  = case coe v0 of
      C_mkSegOK_550 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.SegOK.ok-neu
d_ok'45'neu_548 ::
  T_SegOK_528 ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_548 = erased
-- Once.CCC.Codegen.SlotBudget.segok-idle
d_segok'45'idle_556 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_528
d_segok'45'idle_556 ~v0 v1 ~v2 v3 = du_segok'45'idle_556 v1 v3
du_segok'45'idle_556 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_528
du_segok'45'idle_556 v0 v1
  = coe C_mkSegOK_550 (\ v2 -> coe du_go_572 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.go
d_go_572 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_238
d_go_572 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_go_572 v5 v7
du_go_572 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_238
du_go_572 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_242)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__250 v6 (coe du_go_572 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.segok-++
d_segok'45''43''43'_594 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528 -> T_SegOK_528
d_segok'45''43''43'_594 ~v0 v1 ~v2 v3 v4
  = du_segok'45''43''43'_594 v1 v3 v4
du_segok'45''43''43'_594 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528 -> T_SegOK_528
du_segok'45''43''43'_594 v0 v1 v2
  = coe
      C_mkSegOK_550
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_274 (coe v0) (coe d_ok'45'all_544 v1 v3)
           (coe d_ok'45'all_544 v2 v3))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_612 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 ->
  T_SegOK_528 ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_612 = erased
-- Once.CCC.Codegen.SlotBudget.segok-weaken
d_segok'45'weaken_622 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_528 -> T_SegOK_528
d_segok'45'weaken_622 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_550
      (\ v5 ->
         coe
           d_seg'45'weaken'45'cur_396 v0 v1 v5 v2 v3
           (coe d_ok'45'all_544 v4 v5))
-- Once.CCC.Codegen.SlotBudget.segok-pre
d_segok'45'pre_634 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_528 -> T_SegOK_528
d_segok'45'pre_634 ~v0 v1 ~v2 ~v3 v4 v5
  = du_segok'45'pre_634 v1 v4 v5
du_segok'45'pre_634 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_528 -> T_SegOK_528
du_segok'45'pre_634 v0 v1 v2
  = coe
      du_segok'45''43''43'_594 (coe v0)
      (coe du_segok'45'idle_556 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotBudget.segok-thunk
d_segok'45'thunk_654 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_segok'45'thunk_654 v0 ~v1 ~v2 ~v3 v4 v5
  = du_segok'45'thunk_654 v0 v4 v5
du_segok'45'thunk_654 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
du_segok'45'thunk_654 v0 v1 v2
  = coe C_mkSegOK_550 (coe du_inner_674 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotBudget._.inner
d_inner_674 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> [Integer] -> T_AllSeg_238
d_inner_674 v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inner_674 v0 v4 v5 v6
du_inner_674 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> [Integer] -> T_AllSeg_238
du_inner_674 v0 v1 v2 v3
  = coe
      C__'8759'__250 (coe du_sb'45'none_56)
      (coe
         du_allseg'45''43''43'_258 (coe v1)
         (coe
            d_ok'45'all_544 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__250 (coe du_sb'45'none_56)
            (coe C__'8759'__250 (coe du_sb'45'none_56) (coe C_'91''93'_242))))
-- Once.CCC.Codegen.SlotBudget._.neu
d_neu_682 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_682 = erased
-- Once.CCC.Codegen.SlotBudget.cata-mono
d_cata'45'mono_694 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cata'45'mono_694 v0 v1 ~v2 ~v3 = du_cata'45'mono_694 v0 v1
du_cata'45'mono_694 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_cata'45'mono_694 v0 v1
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
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe addInt (coe (1 :: Integer)) (coe v1)))
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
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_26 v2
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
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v2))))
                      (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.frontier-mono
d_frontier'45'mono_732 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_732 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C__'8728'__30 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                d_frontier'45'mono_732 (coe v0) (coe v6) (coe v9) (coe v3)
                (coe v4))
             (coe
                d_frontier'45'mono_732 (coe v6) (coe v1) (coe v8)
                (coe
                   d_budget'45'of_8
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                         (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                    (coe addInt (coe (2 :: Integer)) (coe v3)))))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 d_frontier'45'mono_732 (coe v0) (coe v11) (coe v8)
                                 (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4))
                              (coe
                                 d_frontier'45'mono_732 (coe v0) (coe v12) (coe v9)
                                 (coe
                                    d_budget'45'of_8
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v11)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                          (coe v8))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                       (coe addInt (coe (3 :: Integer)) (coe v3))))))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 d_frontier'45'mono_732 (coe v0) (coe v11) (coe v8)
                                 (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                              (coe
                                 d_frontier'45'mono_732 (coe v0) (coe v12) (coe v9)
                                 (coe
                                    d_budget'45'of_8
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v11)
                                          (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                          (coe v8))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_inl_56 v7
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.IR.C_inr_62 v7
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.IR.C_case_70 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_frontier'45'mono_732 (coe v10) (coe v1) (coe v8) (coe v3)
                       (coe addInt (coe (2 :: Integer)) (coe v4)))
                    (coe
                       d_frontier'45'mono_732 (coe v11) (coe v1) (coe v9)
                       (coe
                          d_budget'45'of_8
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe v10) (coe v1) (coe v3)
                             (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                (coe v10) (coe v1) (coe v3)
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_curry_86 v8 v9
        -> coe
             seq (coe v9)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (1 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                   (coe addInt (coe (2 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.IR.C_In_96 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       d_frontier'45'mono_732
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                       (coe v1) (coe v8) (coe v3) (coe v4))
                    (coe
                       du_cata'45'mono_694
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'strategy_48
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                       (coe
                          d_budget'45'of_8
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                             (coe v1) (coe v3) (coe v4) (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v6 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_Out_116 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_Hylo_134 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_Fuse_142 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      MAlonzo.Code.Once.IR.C_const_148 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3))
      MAlonzo.Code.Once.IR.C_SigOp_154 v5 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.lt-refl
d_lt'45'refl_876 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lt'45'refl_876 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget.cata-nat-layer-below
d_cata'45'nat'45'layer'45'below_884 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'layer'45'below_884 ~v0 ~v1 ~v2 v3 v4
  = du_cata'45'nat'45'layer'45'below_884 v3 v4
du_cata'45'nat'45'layer'45'below_884 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'layer'45'below_884 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_56)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_90 (coe v0) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_90 (coe v1) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_90 (coe v0) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe v1) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-nat-below
d_cata'45'nat'45'below_910 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_cata'45'nat'45'below_910 v0 v1 v2 v3
  = coe
      du_segok'45'pre_634
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
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
      (coe
         du_segok'45''43''43'_594
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                        (coe addInt (coe (2 :: Integer)) (coe v1))))
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
                                    (coe addInt (coe (3 :: Integer)) (coe v1))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                       (coe addInt (coe (2 :: Integer)) (coe v1))))
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
                                             (coe addInt (coe (3 :: Integer)) (coe v1))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                   (coe addInt (coe (1 :: Integer)) (coe v1))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
         (coe
            du_segok'45'idle_556
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                        (coe addInt (coe (1 :: Integer)) (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                           (coe addInt (coe (2 :: Integer)) (coe v1))))
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
                                       (coe addInt (coe (3 :: Integer)) (coe v1))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                          (coe addInt (coe (2 :: Integer)) (coe v1))))
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
                                                (coe addInt (coe (3 :: Integer)) (coe v1))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                   (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                      (coe addInt (coe (1 :: Integer)) (coe v1))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
            (coe du_descend_930))
         (coe
            du_segok'45'pre_634
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
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
            (coe
               du_segok'45''43''43'_594
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'layer_62
                  (coe v0) (coe (0 :: Integer)))
               (coe
                  du_segok'45'idle_556
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'layer_62
                     (coe v0) (coe (0 :: Integer)))
                  (coe du_layer_934 (coe v0)))
               (coe
                  du_segok'45'pre_634
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                  (coe
                     du_segok'45''43''43'_594 (coe v2)
                     (coe du_at''_928 (coe v0) (coe v2) (coe v3))
                     (coe
                        du_segok'45'pre_634
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                 (coe addInt (coe (4 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                                    (coe addInt (coe (5 :: Integer)) (coe v1))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_56)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                        (coe
                           du_segok'45''43''43'_594
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'layer_62
                              (coe v0) (coe (1 :: Integer)))
                           (coe
                              du_segok'45'idle_556
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'layer_62
                                 (coe v0) (coe (1 :: Integer)))
                              (coe du_layer_934 (coe v0)))
                           (coe
                              du_segok'45'pre_634
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_56)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                              (coe
                                 du_segok'45''43''43'_594 (coe v2)
                                 (coe du_at''_928 (coe v0) (coe v2) (coe v3))
                                 (coe
                                    du_segok'45'idle_556
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_84
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_56)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.p<b
d_p'60'b_924 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p'60'b_924 v0 ~v1 ~v2 ~v3 = du_p'60'b_924 v0
du_p'60'b_924 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p'60'b_924 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_926 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_s'60'b_926 v0 ~v1 ~v2 ~v3 = du_s'60'b_926 v0
du_s'60'b_926 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_926 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_928 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_at''_928 v0 ~v1 v2 v3 = du_at''_928 v0 v2 v3
du_at''_928 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
du_at''_928 v0 v1 v2
  = coe
      d_segok'45'weaken_622 (coe v0)
      (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      (coe v2)
-- Once.CCC.Codegen.SlotBudget._.descend
d_descend_930 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_descend_930 ~v0 ~v1 ~v2 ~v3 = du_descend_930
du_descend_930 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_descend_930
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_56)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_56)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_56)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.SlotBudget._.layer
d_layer_934 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_layer_934 v0 ~v1 ~v2 ~v3 ~v4 = du_layer_934 v0
du_layer_934 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_layer_934 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_56)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'slot_90 (coe du_p'60'b_924 (coe v0)) erased)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_90 (coe du_s'60'b_926 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_90 (coe du_p'60'b_924 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe du_s'60'b_926 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.cata-linear-below
d_cata'45'linear'45'below_952 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_cata'45'linear'45'below_952 v0 v1 v2 v3
  = coe
      du_segok'45''43''43'_594
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
                  (coe addInt (coe (3 :: Integer)) (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                           (coe addInt (coe (1 :: Integer)) (coe v1))))
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
                                       (coe addInt (coe (5 :: Integer)) (coe v0)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v0)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                   (coe addInt (coe (1 :: Integer)) (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                         (coe addInt (coe (5 :: Integer)) (coe v0)))
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
                                                                  (coe v0)))
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
                                                                        (coe v0)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v0)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                           (coe
                                                                              addInt
                                                                              (coe (2 :: Integer))
                                                                              (coe v0)))
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
                                                                                    (coe v1)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe
                                                                                             v1))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
      (coe
         du_segok'45'idle_556
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
                     (coe addInt (coe (3 :: Integer)) (coe v0)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                              (coe addInt (coe (1 :: Integer)) (coe v1))))
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
                                          (coe addInt (coe (5 :: Integer)) (coe v0)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe addInt (coe (2 :: Integer)) (coe v0)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                      (coe addInt (coe (1 :: Integer)) (coe v0)))
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
                                                               (coe v0)))
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
                                                                     (coe v0)))
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
                                                                           (coe v0)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v0)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v0)))
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
                                                                                       (coe v1)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                                                                          (coe
                                                                                             addInt
                                                                                             (coe
                                                                                                (1 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v1))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
         (coe du_descend_982 (coe v0)))
      (coe
         du_segok'45'pre_634
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
         (coe
            du_segok'45''43''43'_594 (coe v2)
            (coe du_at''_980 (coe v0) (coe v2) (coe v3))
            (coe d_ascend_1002 (coe v0) (coe v1) (coe v2) (coe v3))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_966 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> Integer
d_b_966 v0 ~v1 ~v2 ~v3 = du_b_966 v0
du_b_966 :: Integer -> Integer
du_b_966 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.SlotBudget._.p0
d_p0_968 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p0_968 v0 ~v1 ~v2 ~v3 = du_p0_968 v0
du_p0_968 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p0_968 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p1
d_p1_970 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p1_970 v0 ~v1 ~v2 ~v3 = du_p1_970 v0
du_p1_970 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p1_970 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (2 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p2
d_p2_972 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p2_972 v0 ~v1 ~v2 ~v3 = du_p2_972 v0
du_p2_972 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p2_972 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (3 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p3
d_p3_974 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p3_974 v0 ~v1 ~v2 ~v3 = du_p3_974 v0
du_p3_974 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p3_974 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (4 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p4
d_p4_976 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p4_976 v0 ~v1 ~v2 ~v3 = du_p4_976 v0
du_p4_976 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p4_976 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (5 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.p5
d_p5_978 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_p5_978 v0 ~v1 ~v2 ~v3 = du_p5_978 v0
du_p5_978 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_p5_978 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (6 :: Integer)) (coe v0))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_980 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_at''_980 v0 ~v1 v2 v3 = du_at''_980 v0 v2 v3
du_at''_980 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
du_at''_980 v0 v1 v2
  = coe
      d_segok'45'weaken_622 (coe v0) (coe du_b_966 (coe v0)) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      (coe v2)
-- Once.CCC.Codegen.SlotBudget._.descend
d_descend_982 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_descend_982 v0 ~v1 ~v2 ~v3 = du_descend_982 v0
du_descend_982 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_descend_982 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'none_56)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_90 (coe du_p3_974 (coe v0)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe du_p5_978 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_90 (coe du_p2_972 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'slot_90 (coe du_p1_970 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_90 (coe du_p5_978 (coe v0))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_56)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_90
                                                            (coe du_p3_974 (coe v0)) erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_56)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  du_sb'45'slot_90
                                                                  (coe du_p1_970 (coe v0)) erased)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_90
                                                                     (coe du_p3_974 (coe v0))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        du_sb'45'slot_90
                                                                        (coe du_p2_972 (coe v0))
                                                                        erased)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe du_sb'45'none_56)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_56)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe du_sb'45'none_56)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.SlotBudget._.ascend
d_ascend_1002 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_ascend_1002 v0 v1 v2 v3
  = coe
      du_segok'45'pre_634
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
               (coe addInt (coe (2 :: Integer)) (coe v1))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                  (coe addInt (coe (3 :: Integer)) (coe v1))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                  (coe addInt (coe (4 :: Integer)) (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                     (coe addInt (coe (3 :: Integer)) (coe v0)))
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
                              (coe addInt (coe (5 :: Integer)) (coe v0)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe addInt (coe (3 :: Integer)) (coe v0)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v0)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                (coe addInt (coe (5 :: Integer)) (coe v0)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                      (coe addInt (coe (4 :: Integer)) (coe v0)))
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
                                                               (coe v0))
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
                                                                              (coe v0)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_90 (coe du_p4_976 (coe v0)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_90 (coe du_p3_974 (coe v0)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'slot_90 (coe du_p5_978 (coe v0)) erased)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe du_p3_974 (coe v0)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'slot_90 (coe du_p1_970 (coe v0)) erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'slot_90 (coe du_p5_978 (coe v0)) erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_90 (coe du_p4_976 (coe v0))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_56)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_56)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_90
                                                               (coe du_p0_968 (coe v0)) erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_56)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe du_sb'45'none_56)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_56)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_90
                                                                           (coe du_p1_970 (coe v0))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_56)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 du_sb'45'slot_90
                                                                                 (coe
                                                                                    du_p0_968
                                                                                    (coe v0))
                                                                                 erased)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    du_sb'45'none_56)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
      (coe
         du_segok'45''43''43'_594 (coe v2)
         (coe du_at''_980 (coe v0) (coe v2) (coe v3))
         (coe
            du_segok'45'idle_556
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
                        (coe addInt (coe (2 :: Integer)) (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                           (coe addInt (coe (3 :: Integer)) (coe v1))))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.push2-below
d_push2'45'below_1032 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'below_1032 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_push2'45'below_1032 v4 v5 v6
du_push2'45'below_1032 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'below_1032 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_90 (coe v1) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_90 (coe v2) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_90 (coe v1) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_90 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_90 (coe v2) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe v0) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget.pop2-below
d_pop2'45'below_1064 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'below_1064 ~v0 ~v1 v2 = du_pop2'45'below_1064 v2
du_pop2'45'below_1064 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'below_1064 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_90 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_90 (coe v0) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.SlotBudget.wrap-sum-below
d_wrap'45'sum'45'below_1082 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'below_1082 ~v0 ~v1 ~v2 v3 v4
  = du_wrap'45'sum'45'below_1082 v3 v4
du_wrap'45'sum'45'below_1082 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'below_1082 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe du_sb'45'slot_90 (coe v0) erased)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_90 (coe v1) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'slot_90 (coe v0) erased)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_90 (coe v1) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
-- Once.CCC.Codegen.SlotBudget.visit-below
d_visit'45'below_1116 ::
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
d_visit'45'below_1116 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_visit'45'below_1116 v0 v1 v2 v3 v4 v5 v7 v8 v9 v10
du_visit'45'below_1116 ::
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
du_visit'45'below_1116 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v10
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_56)
             (coe du_push2'45'below_1032 (coe v6) (coe v7) (coe v8))
      MAlonzo.Code.Once.Type.C__'8853'__118 v10 v11
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                      (coe v5)))
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
                (coe du_sb'45'none_56)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_56)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_56)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                   (coe v1) (coe v2) (coe v3) (coe v11)
                   (coe addInt (coe (4 :: Integer)) (coe v4))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v10)))
                      (coe v5)))
                (coe
                   du_visit'45'below_1116 (coe v11) (coe v1) (coe v2) (coe v3)
                   (coe addInt (coe (4 :: Integer)) (coe v4))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v10)))
                      (coe v5))
                   (coe v6) (coe v7) (coe v8)
                   (coe du_recG_1190 (coe v10) (coe v11) (coe v4) (coe v9)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                            (coe addInt (coe (1 :: Integer)) (coe v5))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v5)))
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
                      (coe du_sb'45'none_56)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_56)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_56)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_56)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                         (coe v1) (coe v2) (coe v3) (coe v10)
                         (coe addInt (coe (4 :: Integer)) (coe v4))
                         (coe addInt (coe (2 :: Integer)) (coe v5)))
                      (coe
                         du_visit'45'below_1116 (coe v10) (coe v1) (coe v2) (coe v3)
                         (coe addInt (coe (4 :: Integer)) (coe v4))
                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v6) (coe v7)
                         (coe v8) (coe du_recF_1186 (coe v10) (coe v11) (coe v4) (coe v9)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_56)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v10 v11
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
                      (coe v4))
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
                (coe du_sb'45'none_56)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_90
                      (coe du_s'60'b_1226 (coe v10) (coe v11) (coe v4) (coe v9)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_56)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_56)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                   (coe v1) (coe v2) (coe v3) (coe v11)
                   (coe addInt (coe (4 :: Integer)) (coe v4))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v10))
                      (coe v5)))
                (coe
                   du_visit'45'below_1116 (coe v11) (coe v1) (coe v2) (coe v3)
                   (coe addInt (coe (4 :: Integer)) (coe v4))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v10))
                      (coe v5))
                   (coe v6) (coe v7) (coe v8)
                   (coe du_recG_1234 (coe v10) (coe v11) (coe v4) (coe v9)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                         (coe v4))
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
                         du_sb'45'slot_90
                         (coe du_s'60'b_1226 (coe v10) (coe v11) (coe v4) (coe v9)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_56)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_56)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      du_visit'45'below_1116 (coe v10) (coe v1) (coe v2) (coe v3)
                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v6)
                      (coe v7) (coe v8)
                      (coe du_recF_1230 (coe v10) (coe v11) (coe v4) (coe v9)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1186 ::
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
d_recF_1186 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_recF_1186 v0 v1 v5 v11
du_recF_1186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1186 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1190 ::
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
d_recG_1190 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_recG_1190 v0 v1 v5 v11
du_recG_1190 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1190 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1222 ::
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
d_room4_1222 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_room4_1222 v0 v1 v5 v11
du_room4_1222 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1222 v0 v1 v2 v3
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1226 ::
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
d_s'60'b_1226 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_s'60'b_1226 v0 v1 v5 v11
du_s'60'b_1226 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1226 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1222 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1230 ::
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
d_recF_1230 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_recF_1230 v0 v1 v5 v11
du_recF_1230 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1230 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1234 ::
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
d_recG_1234 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_recG_1234 v0 v1 v5 v11
du_recG_1234 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1234 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.rebuild-below
d_rebuild'45'below_1256 ::
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
d_rebuild'45'below_1256 v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_rebuild'45'below_1256 v0 v1 v4 v5 v7 v8
du_rebuild'45'below_1256 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'below_1256 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_sb'45'none_56)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe du_pop2'45'below_1064 (coe v4)
      MAlonzo.Code.Once.Type.C__'8853'__118 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                      (coe v3)))
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
                (coe du_sb'45'none_56)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_56)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_56)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                   (coe v1) (coe v7) (coe addInt (coe (4 :: Integer)) (coe v2))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v6)))
                      (coe v3)))
                (coe
                   du_rebuild'45'below_1256 (coe v7) (coe v1)
                   (coe addInt (coe (4 :: Integer)) (coe v2))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v6)))
                      (coe v3))
                   (coe v4) (coe du_recG_1330 (coe v6) (coe v7) (coe v2) (coe v5)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_wrap'45'sum_154
                      (coe (1 :: Integer)) (coe v2))
                   (coe
                      du_wrap'45'sum'45'below_1082
                      (coe du_s'60'b_1318 (coe v6) (coe v7) (coe v2) (coe v5))
                      (coe du_b'45'ss_1322 (coe v6) (coe v7) (coe v2) (coe v5)))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                               (coe addInt (coe (1 :: Integer)) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v3)))
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
                         (coe du_sb'45'none_56)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_56)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_56)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_56)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                            (coe v1) (coe v6) (coe addInt (coe (4 :: Integer)) (coe v2))
                            (coe addInt (coe (2 :: Integer)) (coe v3)))
                         (coe
                            du_rebuild'45'below_1256 (coe v6) (coe v1)
                            (coe addInt (coe (4 :: Integer)) (coe v2))
                            (coe addInt (coe (2 :: Integer)) (coe v3)) (coe v4)
                            (coe du_recF_1326 (coe v6) (coe v7) (coe v2) (coe v5)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_wrap'45'sum_154
                               (coe (0 :: Integer)) (coe v2))
                            (coe
                               du_wrap'45'sum'45'below_1082
                               (coe du_s'60'b_1318 (coe v6) (coe v7) (coe v2) (coe v5))
                               (coe du_b'45'ss_1322 (coe v6) (coe v7) (coe v2) (coe v5)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_56)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v6 v7
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
                      (coe v2))
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
                (coe du_sb'45'none_56)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe
                      du_sb'45'slot_90
                      (coe du_s'60'b_1362 (coe v6) (coe v7) (coe v2) (coe v5)) erased)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe du_sb'45'none_56)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe du_sb'45'none_56)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                   (coe v1) (coe v6) (coe addInt (coe (4 :: Integer)) (coe v2))
                   (coe v3))
                (coe
                   du_rebuild'45'below_1256 (coe v6) (coe v1)
                   (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3) (coe v4)
                   (coe du_recF_1382 (coe v6) (coe v7) (coe v2) (coe v5)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                            (coe v2))
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
                         du_sb'45'slot_90
                         (coe du_b'45'ss_1366 (coe v6) (coe v7) (coe v2) (coe v5)) erased)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_90
                            (coe du_s'60'b_1362 (coe v6) (coe v7) (coe v2) (coe v5)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_56)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe du_sb'45'none_56)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                         (coe v1) (coe v7) (coe addInt (coe (4 :: Integer)) (coe v2))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v6))
                            (coe v3)))
                      (coe
                         du_rebuild'45'below_1256 (coe v7) (coe v1)
                         (coe addInt (coe (4 :: Integer)) (coe v2))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v6))
                            (coe v3))
                         (coe v4) (coe du_recG_1386 (coe v6) (coe v7) (coe v2) (coe v5)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe
                            du_sb'45'slot_90
                            (coe du_b'45's2_1370 (coe v6) (coe v7) (coe v2) (coe v5)) erased)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe du_sb'45'none_56)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe
                                  du_sb'45'slot_90
                                  (coe du_b'45's3_1376 (coe v6) (coe v7) (coe v2) (coe v5)) erased)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe du_sb'45'none_56)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe
                                        du_sb'45'slot_90
                                        (coe du_b'45'ss_1366 (coe v6) (coe v7) (coe v2) (coe v5))
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe du_sb'45'none_56)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe
                                              du_sb'45'slot_90
                                              (coe
                                                 du_b'45's2_1370 (coe v6) (coe v7) (coe v2)
                                                 (coe v5))
                                              erased)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe du_sb'45'none_56)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe
                                                    du_sb'45'slot_90
                                                    (coe
                                                       du_b'45's3_1376 (coe v6) (coe v7) (coe v2)
                                                       (coe v5))
                                                    erased)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1314 ::
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
d_room4_1314 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_room4_1314 v0 v1 v5 v9
du_room4_1314 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1314 v0 v1 v2 v3
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1318 ::
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
d_s'60'b_1318 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_s'60'b_1318 v0 v1 v5 v9
du_s'60'b_1318 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1318 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1314 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1322 ::
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
d_b'45'ss_1322 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_b'45'ss_1322 v0 v1 v5 v9
du_b'45'ss_1322 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1322 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1314 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1326 ::
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
d_recF_1326 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_recF_1326 v0 v1 v5 v9
du_recF_1326 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1326 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1330 ::
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
d_recG_1330 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_recG_1330 v0 v1 v5 v9
du_recG_1330 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1330 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.room4
d_room4_1358 ::
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
d_room4_1358 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_room4_1358 v0 v1 v5 v9
du_room4_1358 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room4_1358 v0 v1 v2 v3
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
                  (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0)))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe (4 :: Integer))))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.s<b
d_s'60'b_1362 ::
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
d_s'60'b_1362 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_s'60'b_1362 v0 v1 v5 v9
du_s'60'b_1362 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_s'60'b_1362 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (1 :: Integer)) (coe v2)))
      (coe du_room4_1358 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-ss
d_b'45'ss_1366 ::
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
d_b'45'ss_1366 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_b'45'ss_1366 v0 v1 v5 v9
du_b'45'ss_1366 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45'ss_1366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe addInt (coe (2 :: Integer)) (coe v2)))
      (coe du_room4_1358 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s2
d_b'45's2_1370 ::
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
d_b'45's2_1370 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_b'45's2_1370 v0 v1 v5 v9
du_b'45's2_1370 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's2_1370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (3 :: Integer)) (coe v2)))
      (coe du_room4_1358 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.b-s3
d_b'45's3_1376 ::
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
d_b'45's3_1376 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_b'45's3_1376 v0 v1 v5 v9
du_b'45's3_1376 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_b'45's3_1376 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_room4_1358 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.SlotBudget._.recF
d_recF_1382 ::
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
d_recF_1382 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_recF_1382 v0 v1 v5 v9
du_recF_1382 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recF_1382 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget._.recG
d_recG_1386 ::
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
d_recG_1386 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_recG_1386 v0 v1 v5 v9
du_recG_1386 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_recG_1386 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
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
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
               (4 :: Integer)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                  (4 :: Integer)
                  (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                  (addInt
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                     (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))))
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
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) (addInt (coe (4 :: Integer)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (mulInt (coe (4 :: Integer))) (\ v4 v5 -> v4)
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5) (mulInt (coe (4 :: Integer)))
                        (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1))
                        (addInt
                           (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v1)))))))
            (coe v3)))
-- Once.CCC.Codegen.SlotBudget.visit-idle
d_visit'45'idle_1418 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_visit'45'idle_1418 = erased
-- Once.CCC.Codegen.SlotBudget.rebuild-idle
d_rebuild'45'idle_1480 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rebuild'45'idle_1480 = erased
-- Once.CCC.Codegen.SlotBudget.cata-branching-below
d_cata'45'branching'45'below_1538 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_cata'45'branching'45'below_1538 v0 v1 v2 v3 v4
  = coe
      du_segok'45''43''43'_594
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_290
         (coe v0) (coe v1) (coe v2))
      (coe
         du_segok'45'idle_556
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_290
            (coe v0) (coe v1) (coe v2))
         (coe du_I'8321''45'all_1592 (coe v0) (coe v1) (coe v2)))
      (coe
         du_segok'45''43''43'_594 (coe v3)
         (coe du_at''_1588 (coe v0) (coe v1) (coe v3) (coe v4))
         (coe
            du_segok'45'idle_556
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_298
               (coe v1) (coe v2))
            (coe du_I'8322''45'all_1626 (coe v0) (coe v1))))
-- Once.CCC.Codegen.SlotBudget._.b
d_b_1554 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> Integer
d_b_1554 v0 v1 ~v2 ~v3 ~v4 = du_b_1554 v0 v1
du_b_1554 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> Integer -> Integer
du_b_1554 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.SlotBudget._.fixed7
d_fixed7_1556 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7_1556 v0 v1 ~v2 ~v3 ~v4 = du_fixed7_1556 v0 v1
du_fixed7_1556 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7_1556 v0 v1
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
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
            (coe v1)))
-- Once.CCC.Codegen.SlotBudget._.fixed7'
d_fixed7''_1558 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fixed7''_1558 v0 v1 ~v2 ~v3 ~v4 = du_fixed7''_1558 v0 v1
du_fixed7''_1558 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fixed7''_1558 v0 v1 = coe du_fixed7_1556 (coe v0) (coe v1)
-- Once.CCC.Codegen.SlotBudget._.q0
d_q0_1562 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q0_1562 v0 v1 ~v2 ~v3 ~v4 = du_q0_1562 v0 v1
du_q0_1562 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q0_1562 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q1
d_q1_1564 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q1_1564 v0 v1 ~v2 ~v3 ~v4 = du_q1_1564 v0 v1
du_q1_1564 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q1_1564 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q2
d_q2_1566 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q2_1566 v0 v1 ~v2 ~v3 ~v4 = du_q2_1566 v0 v1
du_q2_1566 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q2_1566 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (3 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q3
d_q3_1570 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q3_1570 v0 v1 ~v2 ~v3 ~v4 = du_q3_1570 v0 v1
du_q3_1570 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q3_1570 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (4 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q4
d_q4_1574 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q4_1574 v0 v1 ~v2 ~v3 ~v4 = du_q4_1574 v0 v1
du_q4_1574 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q4_1574 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q5
d_q5_1578 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q5_1578 v0 v1 ~v2 ~v3 ~v4 = du_q5_1578 v0 v1
du_q5_1578 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q5_1578 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (6 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.q6
d_q6_1582 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_q6_1582 v0 v1 ~v2 ~v3 ~v4 = du_q6_1582 v0 v1
du_q6_1582 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_q6_1582 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe addInt (coe (7 :: Integer)) (coe v1)))
      (coe du_fixed7''_1558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotBudget._.walk-room
d_walk'45'room_1586 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_walk'45'room_1586 v0 v1 ~v2 ~v3 ~v4 = du_walk'45'room_1586 v0 v1
du_walk'45'room_1586 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_walk'45'room_1586 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe
         addInt
         (coe
            addInt (coe (7 :: Integer))
            (coe
               mulInt (coe (4 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_fsize_120 (coe v0))))
         (coe v1))
-- Once.CCC.Codegen.SlotBudget._.at'
d_at''_1588 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_at''_1588 v0 v1 ~v2 v3 v4 = du_at''_1588 v0 v1 v3 v4
du_at''_1588 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
du_at''_1588 v0 v1 v2 v3
  = coe
      d_segok'45'weaken_622 (coe v1) (coe du_b_1554 (coe v0) (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v1))
         (coe du_fixed7_1556 (coe v0) (coe v1)))
      (coe v3)
-- Once.CCC.Codegen.SlotBudget._.I₁-idle
d_I'8321''45'idle_1590 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'idle_1590 = erased
-- Once.CCC.Codegen.SlotBudget._.I₁-all
d_I'8321''45'all_1592 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321''45'all_1592 v0 v1 v2 ~v3 ~v4
  = du_I'8321''45'all_1592 v0 v1 v2
du_I'8321''45'all_1592 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321''45'all_1592 v0 v1 v2
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
                     (coe addInt (coe (6 :: Integer)) (coe v1)))
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
                                 (coe addInt (coe (6 :: Integer)) (coe v1)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe addInt (coe (1 :: Integer)) (coe v1)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                       (coe addInt (coe (6 :: Integer)) (coe v1)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (2 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                             (coe addInt (coe (6 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe v1))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                   (coe addInt (coe (3 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'slot_90 (coe du_q3_1570 (coe v0) (coe v1)) erased)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_90 (coe du_q6_1582 (coe v0) (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_90 (coe du_q6_1582 (coe v0) (coe v1)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe du_q1_1564 (coe v0) (coe v1)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'slot_90 (coe du_q6_1582 (coe v0) (coe v1)) erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90 (coe du_q2_1566 (coe v0) (coe v1))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90 (coe du_q6_1582 (coe v0) (coe v1))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_90 (coe du_q0_1562 (coe v0) (coe v1))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_90
                                                   (coe du_q3_1570 (coe v0) (coe v1)) erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_push2_136 (coe v1)
            (coe addInt (coe (4 :: Integer)) (coe v1))
            (coe addInt (coe (5 :: Integer)) (coe v1)))
         (coe
            du_push2'45'below_1032 (coe du_q0_1562 (coe v0) (coe v1))
            (coe du_q4_1574 (coe v0) (coe v1))
            (coe du_q5_1578 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 (coe v2)))
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
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                              (coe addInt (coe (1 :: Integer)) (coe v2))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                 (coe v1))
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
                                          (coe addInt (coe (3 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                             (coe addInt (coe (3 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'none_56)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'slot_90 (coe du_q0_1562 (coe v0) (coe v1)) erased)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'slot_90 (coe du_q0_1562 (coe v0) (coe v1)) erased)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_56)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90 (coe du_q3_1570 (coe v0) (coe v1))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90 (coe du_q3_1570 (coe v0) (coe v1))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_push2_136
                  (coe addInt (coe (1 :: Integer)) (coe v1))
                  (coe addInt (coe (4 :: Integer)) (coe v1))
                  (coe addInt (coe (5 :: Integer)) (coe v1)))
               (coe
                  du_push2'45'below_1032 (coe du_q1_1564 (coe v0) (coe v1))
                  (coe du_q4_1574 (coe v0) (coe v1))
                  (coe du_q5_1578 (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                        (coe addInt (coe (3 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'slot_90 (coe du_q3_1570 (coe v0) (coe v1)) erased)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe du_sb'45'none_56)
                        (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                        (coe v1) (coe addInt (coe (4 :: Integer)) (coe v1))
                        (coe addInt (coe (5 :: Integer)) (coe v1)) (coe v0)
                        (coe addInt (coe (7 :: Integer)) (coe v1))
                        (coe addInt (coe (4 :: Integer)) (coe v2)))
                     (coe
                        du_visit'45'below_1116 (coe v0) (coe v1)
                        (coe addInt (coe (4 :: Integer)) (coe v1))
                        (coe addInt (coe (5 :: Integer)) (coe v1))
                        (coe addInt (coe (7 :: Integer)) (coe v1))
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe du_q0_1562 (coe v0) (coe v1))
                        (coe du_q4_1574 (coe v0) (coe v1))
                        (coe du_q5_1578 (coe v0) (coe v1))
                        (coe du_walk'45'room_1586 (coe v0) (coe v1)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                    (coe addInt (coe (1 :: Integer)) (coe v2))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe du_sb'45'none_56)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                    (coe addInt (coe (2 :: Integer)) (coe v2))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                    (coe addInt (coe (1 :: Integer)) (coe v1)))
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
                                             (coe addInt (coe (3 :: Integer)) (coe v2))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                (coe addInt (coe (1 :: Integer)) (coe v1)))
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
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'slot_90 (coe du_q1_1564 (coe v0) (coe v1)) erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_56)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_90 (coe du_q1_1564 (coe v0) (coe v1))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_56)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                                 (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v0)
                                 (coe addInt (coe (7 :: Integer)) (coe v1))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160
                                          (coe v0)))
                                    (coe v2)))
                              (coe
                                 du_rebuild'45'below_1256 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v1))
                                 (coe addInt (coe (7 :: Integer)) (coe v1))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160
                                          (coe v0)))
                                    (coe v2))
                                 (coe du_q2_1566 (coe v0) (coe v1))
                                 (coe du_walk'45'room_1586 (coe v0) (coe v1)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe du_sb'45'none_56)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.SlotBudget._.I₂-all
d_I'8322''45'all_1626 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322''45'all_1626 v0 v1 ~v2 ~v3 ~v4
  = du_I'8322''45'all_1626 v0 v1
du_I'8322''45'all_1626 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322''45'all_1626 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_push2_136
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         du_push2'45'below_1032 (coe du_q2_1566 (coe v0) (coe v1))
         (coe du_q4_1574 (coe v0) (coe v1))
         (coe du_q5_1578 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe du_sb'45'none_56)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe du_sb'45'none_56)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe du_sb'45'slot_90 (coe du_q2_1566 (coe v0) (coe v1)) erased)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe du_sb'45'none_56)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe du_sb'45'none_56)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.CCC.Codegen.SlotBudget.cata-slots-below
d_cata'45'slots'45'below_1638 ::
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SegOK_528 -> T_SegOK_528
d_cata'45'slots'45'below_1638 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_20
        -> coe v4
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_22
        -> coe
             d_cata'45'nat'45'below_910 (coe v1) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_24
        -> coe
             d_cata'45'linear'45'below_952 (coe v1) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_26 v5
        -> coe
             d_cata'45'branching'45'below_1538 (coe v5) (coe v1) (coe v2)
             (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.slots-below
d_slots'45'below_1684 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer -> T_SegOK_528
d_slots'45'below_1684 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v0) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_56)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C__'8728'__30 v6 v8 v9
        -> coe
             du_segok'45''43''43'_594
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
             (coe
                d_segok'45'weaken_622
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                (coe
                   d_budget'45'of_8
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v1) (coe v3) (coe v4)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v6 v8 v9)))
                (coe
                   d_trace'45'of_12
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                      (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                (coe
                   d_frontier'45'mono_732 (coe v6) (coe v1) (coe v8)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                         (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                            (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))))
                (coe
                   d_slots'45'below_1684 (coe v0) (coe v6) (coe v9) (coe v3)
                   (coe v4)))
             (coe
                du_segok'45'pre_634
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe du_sb'45'none_56)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
                (coe
                   d_slots'45'below_1684 (coe v6) (coe v1) (coe v8)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                         (coe v0) (coe v6) (coe v3) (coe v4) (coe v9)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                            (coe v0) (coe v6) (coe v3) (coe v4) (coe v9))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_634
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v3))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v3)))
                                       (coe
                                          d_h_1726 (coe v0) (coe v11) (coe v12) (coe v8) (coe v9)
                                          (coe v3) (coe v4)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_594
                              (coe
                                 d_trace'45'of_12
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                    (coe v4) (coe v8)))
                              (coe
                                 d_segok'45'weaken_622
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    d_budget'45'of_8
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v1) (coe v3) (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9
                                          v10)))
                                 (coe
                                    d_trace'45'of_12
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (3 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    d_frontier'45'mono_732 (coe v0) (coe v12) (coe v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v11)
                                          (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                          (coe v8)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                             (coe v0) (coe v11)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                             (coe v8)))))
                                 (coe
                                    d_slots'45'below_1684 (coe v0) (coe v11) (coe v8)
                                    (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)))
                              (coe
                                 du_segok'45'pre_634
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
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_90
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          (coe
                                             d_h_1726 (coe v0) (coe v11) (coe v12) (coe v8) (coe v9)
                                             (coe v3) (coe v4)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                d_h_1726 (coe v0) (coe v11) (coe v12) (coe v8)
                                                (coe v9) (coe v3) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_594
                                    (coe
                                       d_trace'45'of_12
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v12)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                   (coe v0) (coe v11)
                                                   (coe addInt (coe (3 :: Integer)) (coe v3))
                                                   (coe v4) (coe v8))))
                                          (coe v9)))
                                    (coe
                                       d_slots'45'below_1684 (coe v0) (coe v12) (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                             (coe v0) (coe v11)
                                             (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)) (coe v4)
                                                (coe v8)))))
                                    (coe
                                       du_segok'45'idle_556
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90
                                             (coe
                                                d_h_1726 (coe v0) (coe v11) (coe v12) (coe v8)
                                                (coe v9) (coe v3) (coe v4))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_90
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v3)))
                                                   (coe
                                                      d_h_1726 (coe v0) (coe v11) (coe v12) (coe v8)
                                                      (coe v9) (coe v3) (coe v4)))
                                                (coe
                                                   (\ v13 v14 ->
                                                      d_h_1726
                                                        (coe v0) (coe v11) (coe v12) (coe v8)
                                                        (coe v9) (coe v3) (coe v4))))
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_634
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                    (coe v3))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe addInt (coe (1 :: Integer)) (coe v3)))
                                       (coe
                                          d_h_1750 (coe v0) (coe v11) (coe v12) (coe v8) (coe v9)
                                          (coe v3) (coe v4)))
                                    erased)
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                           (coe
                              du_segok'45''43''43'_594
                              (coe
                                 d_trace'45'of_12
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                    (coe v4) (coe v8)))
                              (coe
                                 d_segok'45'weaken_622
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    d_budget'45'of_8
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v1) (coe v3) (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9
                                          v10)))
                                 (coe
                                    d_trace'45'of_12
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v0) (coe v11) (coe addInt (coe (4 :: Integer)) (coe v3))
                                       (coe v4) (coe v8)))
                                 (coe
                                    d_frontier'45'mono_732 (coe v0) (coe v12) (coe v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v11)
                                          (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                          (coe v8)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                             (coe v0) (coe v11)
                                             (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                             (coe v8)))))
                                 (coe
                                    d_slots'45'below_1684 (coe v0) (coe v11) (coe v8)
                                    (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)))
                              (coe
                                 du_segok'45'pre_634
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
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe
                                       du_sb'45'slot_90
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          (coe
                                             d_h_1750 (coe v0) (coe v11) (coe v12) (coe v8) (coe v9)
                                             (coe v3) (coe v4)))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                d_h_1750 (coe v0) (coe v11) (coe v12) (coe v8)
                                                (coe v9) (coe v3) (coe v4)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                 (coe
                                    du_segok'45''43''43'_594
                                    (coe
                                       d_trace'45'of_12
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe v0) (coe v12)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                   (coe v0) (coe v11)
                                                   (coe addInt (coe (4 :: Integer)) (coe v3))
                                                   (coe v4) (coe v8))))
                                          (coe v9)))
                                    (coe
                                       d_slots'45'below_1684 (coe v0) (coe v12) (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                             (coe v0) (coe v11)
                                             (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                                (coe v8)))))
                                    (coe
                                       du_segok'45'idle_556
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                                   (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
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
                                                                  (coe v3)))
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
                                                                        (coe v3)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                (coe
                                                   d_h_1750 (coe v0) (coe v11) (coe v12) (coe v8)
                                                   (coe v9) (coe v3) (coe v4)))
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_90
                                                   (coe
                                                      d_h_1750 (coe v0) (coe v11) (coe v12) (coe v8)
                                                      (coe v9) (coe v3) (coe v4))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_56)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_90
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v3)))
                                                            (coe
                                                               d_h_1750 (coe v0) (coe v11) (coe v12)
                                                               (coe v8) (coe v9) (coe v3) (coe v4)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_56)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_90
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                  (coe
                                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v3)))
                                                                  (coe
                                                                     d_h_1750 (coe v0) (coe v11)
                                                                     (coe v12) (coe v8) (coe v9)
                                                                     (coe v3) (coe v4)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_56)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_90
                                                                     (coe
                                                                        d_h_1750 (coe v0) (coe v11)
                                                                        (coe v12) (coe v8) (coe v9)
                                                                        (coe v3) (coe v4))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v8)) (coe v1)
                          (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_fst_44)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v7) (coe v1)) (coe v1)
                          (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_snd_50)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_556
                           (coe
                              d_trace'45'of_12
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v9))
                                 (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_inl_56 v7)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                (\ v10 v11 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v10)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'idle_556
                           (coe
                              d_trace'45'of_12
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v9))
                                 (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_inl_56 v7)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_90
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_56)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_90
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v3)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'idle_556
                           (coe
                              d_trace'45'of_12
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v8) (coe v0))
                                 (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_inr_62 v7)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                (\ v10 v11 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v10)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'idle_556
                           (coe
                              d_trace'45'of_12
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v8) (coe v0))
                                 (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_inr_62 v7)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe
                                                      du_sb'45'slot_90
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                      erased)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_56)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_90
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v3)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_70 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    du_segok'45'pre_634
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe v4)))
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
                       (coe du_sb'45'none_56)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe du_sb'45'none_56)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe du_sb'45'none_56)
                             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                    (coe
                       du_segok'45''43''43'_594
                       (coe
                          d_trace'45'of_12
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe v11) (coe v1)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v10) (coe v1) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                      (coe v10) (coe v1) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8))))
                             (coe v9)))
                       (coe
                          d_slots'45'below_1684 (coe v11) (coe v1) (coe v9)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                (coe v10) (coe v1) (coe v3)
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v10) (coe v1) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))))
                       (coe
                          du_segok'45'pre_634
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                   (coe addInt (coe (1 :: Integer)) (coe v4))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                      (coe v4)))
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
                             (coe du_sb'45'none_56)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe du_sb'45'none_56)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_56)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe du_sb'45'none_56)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                          (coe
                             du_segok'45''43''43'_594
                             (coe
                                d_trace'45'of_12
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v10) (coe v1) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                             (coe
                                d_segok'45'weaken_622
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                      (coe v10) (coe v1) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                                (coe
                                   d_budget'45'of_8
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                      (coe v0) (coe v1) (coe v3) (coe v4)
                                      (coe MAlonzo.Code.Once.IR.C_case_70 v8 v9)))
                                (coe
                                   d_trace'45'of_12
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                      (coe v10) (coe v1) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                                (coe
                                   d_frontier'45'mono_732 (coe v11) (coe v1) (coe v9)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                         (coe v10) (coe v1) (coe v3)
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                            (coe v10) (coe v1) (coe v3)
                                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))))
                                (coe
                                   d_slots'45'below_1684 (coe v10) (coe v1) (coe v8) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4))))
                             (coe
                                du_segok'45'idle_556
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176
                                         (coe addInt (coe (1 :: Integer)) (coe v4))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe du_sb'45'none_56)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_terminal_74)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v1) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_initial_78)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_56)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_curry_86 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           du_segok'45'pre_634
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
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244
                                       (coe v4))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v3)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                   (coe addInt (coe (1 :: Integer)) (coe v4))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe
                                             du_sb'45'slot_90
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                (\ v12 v13 ->
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe addInt (coe (2 :: Integer)) (coe v12)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
                           (coe
                              du_segok'45'thunk_654
                              (coe
                                 d_budget'45'of_8
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v1) (coe v3) (coe v4)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v8 v9)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                          (coe v11) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))))
                              (coe
                                 d_slots'45'below_1684
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                 (coe v11) (coe v8) (coe (0 :: Integer))
                                 (coe addInt (coe (2 :: Integer)) (coe v4))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           du_segok'45'pre_634
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
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252
                                       (coe (2 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204
                                          (coe addInt (coe (1 :: Integer)) (coe v3)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                                                (coe v3))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244
                                                      (coe v4))
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
                                                               (coe v3)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v4))))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe
                                          du_sb'45'slot_90
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe
                                                du_sb'45'slot_90
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                   (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                erased)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe du_sb'45'none_56)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_56)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe du_sb'45'none_56)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe
                                                            du_sb'45'slot_90
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v3)))
                                                            erased)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe du_sb'45'none_56)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
                           (coe
                              du_segok'45'thunk_654
                              (coe
                                 d_budget'45'of_8
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                    (coe v0) (coe v1) (coe v3) (coe v4)
                                    (coe MAlonzo.Code.Once.IR.C_curry_86 v8 v9)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                          (coe v11) (coe (0 :: Integer))
                                          (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v8)))))
                              (coe
                                 d_slots'45'below_1684
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                 (coe v11) (coe v8) (coe (0 :: Integer))
                                 (coe addInt (coe (2 :: Integer)) (coe v4))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
                      -> coe
                           du_segok'45'idle_556
                           (coe
                              d_trace'45'of_12
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v9) (coe v1))
                                    (coe v9))
                                 (coe v1) (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_sb'45'none_56)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe
                                    du_sb'45'slot_90
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                    erased)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe du_sb'45'none_56)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe du_sb'45'none_56)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe du_sb'45'none_56)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe du_sb'45'none_56)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe
                                                   du_sb'45'slot_90
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe addInt (coe (2 :: Integer)) (coe v3)))
                                                   erased)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe du_sb'45'none_56)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe
                                                         du_sb'45'slot_90
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v3)))
                                                         erased)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe du_sb'45'none_56)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               du_sb'45'slot_90
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v3)))
                                                               erased)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe du_sb'45'none_56)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     du_sb'45'slot_90
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v3)))
                                                                     erased)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe du_sb'45'none_56)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           du_sb'45'slot_90
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v3)))
                                                                           erased)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe du_sb'45'none_56)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe du_sb'45'none_56)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v1) (coe v3) (coe v4)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v6 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                          (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v6)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    d_cata'45'slots'45'below_1638
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'strategy_48
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                          (coe v1) (coe v3) (coe v4) (coe v8)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                             (coe v1) (coe v3) (coe v4) (coe v8))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                                (coe v1) (coe v3) (coe v4) (coe v8)))))
                    (coe
                       d_slots'45'below_1684
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                       (coe v1) (coe v8) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v6 v8
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v1) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_Para_112 v6 v8)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Out_116 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                          (coe v3) (coe v4) (coe MAlonzo.Code.Once.IR.C_Out_116 v6)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v1) (coe v3) (coe v4)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_120 v6 v7)))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v8
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v1) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_Ana_126 v6 v8)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Hylo_134 v5 v7 v8 v10 v11
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v1) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_134 v5 v7 v8 v10 v11)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Fuse_142 v5 v7 v8 v10 v11
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v0) (coe v1) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_142 v5 v7 v8 v10 v11)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v5
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3) (coe v4) (coe v2)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_56)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_const_148 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v3) (coe v4)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v6 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    du_segok'45'idle_556
                    (coe
                       d_trace'45'of_12
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v3) (coe v4)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v6 v7)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe du_sb'45'none_56)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_154 v5 v6 v7
        -> coe
             du_segok'45'idle_556
             (coe
                d_trace'45'of_12
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v5))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6)) (coe v3)
                   (coe v4) (coe v2)))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_sb'45'none_56)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1726 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1726 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_732 (coe v0) (coe v1) (coe v3)
         (coe addInt (coe (3 :: Integer)) (coe v5)) (coe v6))
      (coe
         d_frontier'45'mono_732 (coe v0) (coe v2) (coe v4)
         (coe
            d_budget'45'of_8
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
               (coe v0) (coe v1) (coe addInt (coe (3 :: Integer)) (coe v5))
               (coe v6) (coe v3)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                  (coe v0) (coe v1) (coe addInt (coe (3 :: Integer)) (coe v5))
                  (coe v6) (coe v3)))))
-- Once.CCC.Codegen.SlotBudget._.h
d_h_1750 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_h_1750 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         d_frontier'45'mono_732 (coe v0) (coe v1) (coe v3)
         (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
      (coe
         d_frontier'45'mono_732 (coe v0) (coe v2) (coe v4)
         (coe
            d_budget'45'of_8
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
               (coe v0) (coe v1) (coe addInt (coe (4 :: Integer)) (coe v5))
               (coe v6) (coe v3)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                  (coe v0) (coe v1) (coe addInt (coe (4 :: Integer)) (coe v5))
                  (coe v6) (coe v3)))))
-- Once.CCC.Codegen.SlotBudget.trace-lookup
d_trace'45'lookup_1918 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_trace'45'lookup_1918 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_trace'45'lookup_1918 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.fetch-at
d_fetch'45'at_1926 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch'45'at_1926 = coe d_trace'45'lookup_1918
-- Once.CCC.Codegen.SlotBudget.seg-at
d_seg'45'at_1928 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_SegState_160 -> T_SegState_160
d_seg'45'at_1928 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       d_seg'45'at_1928 (coe v5) (coe v3)
                       (coe d_seg'45'step_202 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotBudget.seg-at-suc
d_seg'45'at'45'suc_1950 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_SegState_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_1950 = erased
-- Once.CCC.Codegen.SlotBudget.idle-seg-at
d_idle'45'seg'45'at_1978 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_1978 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_2012 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  T_SegState_160 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_2012 = erased
-- Once.CCC.Codegen.SlotBudget.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_2048 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  T_SegState_160 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_2048 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ˡ
d_fetch'45''43''43''737'_2072 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_2072 = erased
-- Once.CCC.Codegen.SlotBudget.fetch-++ʳ
d_fetch'45''43''43''691'_2100 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_2100 = erased
-- Once.CCC.Codegen.SlotBudget.split-pos
d_split'45'pos_2120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_2120 v0 v1
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
                    (let v5 = d_split'45'pos_2120 (coe v3) (coe v4) in
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
d_allseg'45'at_2164 ::
  T_SegState_160 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_AllSeg_238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_28
d_allseg'45'at_2164 ~v0 v1 v2 ~v3 v4 ~v5
  = du_allseg'45'at_2164 v1 v2 v4
du_allseg'45'at_2164 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_AllSeg_238 -> T_SlotBelow_28
du_allseg'45'at_2164 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__250 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__250 v9 v10
                         -> coe du_allseg'45'at_2164 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotBudget.ir-slots-below-seg
d_ir'45'slots'45'below'45'seg_2194 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_SegOK_528
d_ir'45'slots'45'below'45'seg_2194 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
              (coe v0) (coe v1) (coe (0 :: Integer)) (coe (0 :: Integer))
              (coe v2) in
    coe
      (let v4
             = d_slots'45'below_1684
                 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                 (coe (0 :: Integer)) in
       coe
         (case coe v3 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
              -> case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                     -> coe seq (coe v8) (coe v4)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Codegen.SlotBudget.emitted-slot-seg
d_emitted'45'slot'45'seg_2218 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'seg_2218 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_emitted'45'slot'45'seg_2218 v0 v1 v2 v3 v5
du_emitted'45'slot'45'seg_2218 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'seg_2218 v0 v1 v2 v3 v4
  = coe
      d_below_44
      (coe
         du_allseg'45'at_2164
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_682
            (coe v0) (coe v1) (coe v2))
         (coe v3)
         (coe
            d_ok'45'all_544
            (d_ir'45'slots'45'below'45'seg_2194 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      v4 erased
