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

module MAlonzo.Code.Once.CCC.Codegen.SlotSeg where

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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.SlotSeg.SlotBelow
d_SlotBelow_12 a0 a1 = ()
data T_SlotBelow_12
  = C_mkSlotBelow_34 (Integer ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                     (Integer ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.SlotSeg.SlotBelow.below
d_below_28 ::
  T_SlotBelow_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_28 v0
  = case coe v0 of
      C_mkSlotBelow_34 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SlotBelow.pair-below
d_pair'45'below_32 ::
  T_SlotBelow_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pair'45'below_32 v0
  = case coe v0 of
      C_mkSlotBelow_34 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.sb-none
d_sb'45'none_40 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_12
d_sb'45'none_40 ~v0 ~v1 ~v2 = du_sb'45'none_40
du_sb'45'none_40 :: T_SlotBelow_12
du_sb'45'none_40
  = coe
      C_mkSlotBelow_34 (coe (\ v0 v1 -> coe du_go_56))
      (coe (\ v0 v1 -> coe du_go_56))
-- Once.CCC.Codegen.SlotSeg._.go
d_go_56 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_go_56
du_go_56 :: AgdaAny
du_go_56 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.sb-slot
d_sb'45'slot_74 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_12
d_sb'45'slot_74 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sb'45'slot_74 v4 v5
du_sb'45'slot_74 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SlotBelow_12
du_sb'45'slot_74 v0 v1
  = coe C_mkSlotBelow_34 (coe (\ v2 v3 -> v0)) (coe v1)
-- Once.CCC.Codegen.SlotSeg._.just-inj
d_just'45'inj_92 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_92 = erased
-- Once.CCC.Codegen.SlotSeg.sb-le
d_sb'45'le_106 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_12 -> T_SlotBelow_12
d_sb'45'le_106 ~v0 ~v1 ~v2 v3 v4 = du_sb'45'le_106 v3 v4
du_sb'45'le_106 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_12 -> T_SlotBelow_12
du_sb'45'le_106 v0 v1
  = coe
      C_mkSlotBelow_34
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_below_28 v1 v2 erased) (coe v0)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
              (coe d_pair'45'below_32 v1 v2 erased) (coe v0)))
-- Once.CCC.Codegen.SlotSeg.SegState
d_SegState_120 = ()
data T_SegState_120 = C_mkSeg_130 Integer [Integer]
-- Once.CCC.Codegen.SlotSeg.SegState.cur
d_cur_126 :: T_SegState_120 -> Integer
d_cur_126 v0
  = case coe v0 of
      C_mkSeg_130 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegState.saved
d_saved_128 :: T_SegState_120 -> [Integer]
d_saved_128 v0
  = case coe v0 of
      C_mkSeg_130 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegAction
d_SegAction_132 = ()
data T_SegAction_132
  = C_seg'45'id_134 | C_seg'45'push_136 Integer | C_seg'45'pop_138
-- Once.CCC.Codegen.SlotSeg.seg-action
d_seg'45'action_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_SegAction_132
d_seg'45'action_140 v0
  = let v1 = coe C_seg'45'id_134 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v3 v4
                  -> coe C_seg'45'push_136 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v3
                  -> coe C_seg'45'pop_138
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v3
                  -> coe C_seg'45'push_136 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotSeg.pop-with
d_pop'45'with_146 :: [Integer] -> T_SegState_120 -> T_SegState_120
d_pop'45'with_146 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_130 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply
d_seg'45'apply_154 ::
  T_SegAction_132 -> T_SegState_120 -> T_SegState_120
d_seg'45'apply_154 v0 v1
  = case coe v0 of
      C_seg'45'id_134 -> coe v1
      C_seg'45'push_136 v2
        -> coe
             C_mkSeg_130 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_126 (coe v1)) (coe d_saved_128 (coe v1)))
      C_seg'45'pop_138
        -> coe d_pop'45'with_146 (coe d_saved_128 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-step
d_seg'45'step_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_SegState_120 -> T_SegState_120
d_seg'45'step_164 v0 v1
  = coe
      d_seg'45'apply_154 (coe d_seg'45'action_140 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotSeg.seg-fold
d_seg'45'fold_170 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegState_120 -> T_SegState_120
d_seg'45'fold_170 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_seg'45'fold_170 (coe v3)
             (coe d_seg'45'step_164 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-fold-++
d_seg'45'fold'45''43''43'_186 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_186 = erased
-- Once.CCC.Codegen.SlotSeg.AllSeg
d_AllSeg_200 a0 a1 = ()
data T_AllSeg_200
  = C_'91''93'_204 | C__'8759'__212 T_SlotBelow_12 T_AllSeg_200
-- Once.CCC.Codegen.SlotSeg.allseg-++
d_allseg'45''43''43'_220 ::
  T_SegState_120 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_AllSeg_200 -> T_AllSeg_200 -> T_AllSeg_200
d_allseg'45''43''43'_220 ~v0 v1 ~v2 v3 v4
  = du_allseg'45''43''43'_220 v1 v3 v4
du_allseg'45''43''43'_220 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_AllSeg_200 -> T_AllSeg_200 -> T_AllSeg_200
du_allseg'45''43''43'_220 v0 v1 v2
  = case coe v1 of
      C_'91''93'_204 -> coe v2
      C__'8759'__212 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__212 v6
                    (coe du_allseg'45''43''43'_220 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.allseg-++bal
d_allseg'45''43''43'bal_236 ::
  T_SegState_120 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_200 -> T_AllSeg_200 -> T_AllSeg_200
d_allseg'45''43''43'bal_236 ~v0 v1 ~v2 ~v3 v4 v5
  = du_allseg'45''43''43'bal_236 v1 v4 v5
du_allseg'45''43''43'bal_236 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_AllSeg_200 -> T_AllSeg_200 -> T_AllSeg_200
du_allseg'45''43''43'bal_236 v0 v1 v2
  = coe du_allseg'45''43''43'_220 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotSeg.SavedLE
d_SavedLE_246 a0 a1 = ()
data T_SavedLE_246
  = C_'91''93'_248 |
    C__'8759'__258 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_246
-- Once.CCC.Codegen.SlotSeg.SegLE
d_SegLE_264 a0 a1 = ()
data T_SegLE_264
  = C_mkSegLE_278 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_246
-- Once.CCC.Codegen.SlotSeg.SegLE.cur-le
d_cur'45'le_274 ::
  T_SegLE_264 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_274 v0
  = case coe v0 of
      C_mkSegLE_278 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegLE.saved-le
d_saved'45'le_276 :: T_SegLE_264 -> T_SavedLE_246
d_saved'45'le_276 v0
  = case coe v0 of
      C_mkSegLE_278 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.saved-le-refl
d_saved'45'le'45'refl_282 :: [Integer] -> T_SavedLE_246
d_saved'45'le'45'refl_282 v0
  = case coe v0 of
      [] -> coe C_'91''93'_248
      (:) v1 v2
        -> coe
             C__'8759'__258
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (d_saved'45'le'45'refl_282 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.pop-mono
d_pop'45'mono_296 ::
  T_SegState_120 ->
  T_SegState_120 ->
  [Integer] ->
  [Integer] -> T_SavedLE_246 -> T_SegLE_264 -> T_SegLE_264
d_pop'45'mono_296 ~v0 ~v1 v2 v3 v4 v5
  = du_pop'45'mono_296 v2 v3 v4 v5
du_pop'45'mono_296 ::
  [Integer] ->
  [Integer] -> T_SavedLE_246 -> T_SegLE_264 -> T_SegLE_264
du_pop'45'mono_296 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__258 v10 v11 -> coe C_mkSegLE_278 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply-mono
d_seg'45'apply'45'mono_318 ::
  T_SegAction_132 ->
  T_SegState_120 -> T_SegState_120 -> T_SegLE_264 -> T_SegLE_264
d_seg'45'apply'45'mono_318 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_134 -> coe v3
      C_seg'45'push_136 v4
        -> coe
             C_mkSegLE_278
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_126 (coe d_seg'45'apply_154 (coe v0) (coe v1))))
             (coe
                C__'8759'__258 (d_cur'45'le_274 (coe v3))
                (d_saved'45'le_276 (coe v3)))
      C_seg'45'pop_138
        -> coe
             du_pop'45'mono_296 (coe d_saved_128 (coe v1))
             (coe d_saved_128 (coe v2)) (coe d_saved'45'le_276 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken
d_seg'45'weaken_338 ::
  T_SegState_120 ->
  T_SegState_120 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegLE_264 -> T_AllSeg_200 -> T_AllSeg_200
d_seg'45'weaken_338 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_204 -> coe C_'91''93'_204
      C__'8759'__212 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__212
                    (coe du_sb'45'le_106 (coe d_cur'45'le_274 (coe v3)) (coe v8))
                    (d_seg'45'weaken_338
                       (coe
                          d_seg'45'apply_154 (coe d_seg'45'action_140 (coe v10)) (coe v0))
                       (coe d_seg'45'step_164 (coe v10) (coe v1)) (coe v11)
                       (coe
                          d_seg'45'apply'45'mono_318 (coe d_seg'45'action_140 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken-cur
d_seg'45'weaken'45'cur_358 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_200 -> T_AllSeg_200
d_seg'45'weaken'45'cur_358 v0 v1 v2 v3 v4
  = coe
      d_seg'45'weaken_338 (coe C_mkSeg_130 (coe v0) (coe v2))
      (coe C_mkSeg_130 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_278 (coe v4) (coe d_saved'45'le'45'refl_282 (coe v2)))
-- Once.CCC.Codegen.SlotSeg.is-id?
d_is'45'id'63'_364 :: T_SegAction_132 -> Bool
d_is'45'id'63'_364 v0
  = case coe v0 of
      C_seg'45'id_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_136 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-idle?
d_seg'45'idle'63'_366 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> Bool
d_seg'45'idle'63'_366 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is'45'id'63'_364 (coe d_seg'45'action_140 (coe v1)))
             (coe d_seg'45'idle'63'_366 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.idle-step
d_idle'45'step_376 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_376 = erased
-- Once.CCC.Codegen.SlotSeg._.go
d_go_390 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_120 ->
  T_SegAction_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_390 = erased
-- Once.CCC.Codegen.SlotSeg.idle-head
d_idle'45'head_396 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_396 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-fst
d_'8743''45'fst_412 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_412 = erased
-- Once.CCC.Codegen.SlotSeg.idle-tail
d_idle'45'tail_422 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_422 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-snd
d_'8743''45'snd_438 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_438 = erased
-- Once.CCC.Codegen.SlotSeg.idle-++
d_idle'45''43''43'_450 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_450 = erased
-- Once.CCC.Codegen.SlotSeg.idle-neutral
d_idle'45'neutral_474 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_474 = erased
-- Once.CCC.Codegen.SlotSeg.SegOK
d_SegOK_490 a0 a1 = ()
newtype T_SegOK_490 = C_mkSegOK_512 ([Integer] -> T_AllSeg_200)
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-all
d_ok'45'all_506 :: T_SegOK_490 -> [Integer] -> T_AllSeg_200
d_ok'45'all_506 v0
  = case coe v0 of
      C_mkSegOK_512 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-neu
d_ok'45'neu_510 ::
  T_SegOK_490 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_510 = erased
-- Once.CCC.Codegen.SlotSeg.segok-idle
d_segok'45'idle_518 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_490
d_segok'45'idle_518 ~v0 v1 ~v2 v3 = du_segok'45'idle_518 v1 v3
du_segok'45'idle_518 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_490
du_segok'45'idle_518 v0 v1
  = coe C_mkSegOK_512 (\ v2 -> coe du_go_534 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotSeg._.go
d_go_534 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_200
d_go_534 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_go_534 v5 v7
du_go_534 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_200
du_go_534 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_204)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__212 v6 (coe du_go_534 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.segok-++
d_segok'45''43''43'_556 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490 -> T_SegOK_490
d_segok'45''43''43'_556 ~v0 v1 ~v2 v3 v4
  = du_segok'45''43''43'_556 v1 v3 v4
du_segok'45''43''43'_556 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490 -> T_SegOK_490
du_segok'45''43''43'_556 v0 v1 v2
  = coe
      C_mkSegOK_512
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_236 (coe v0) (coe d_ok'45'all_506 v1 v3)
           (coe d_ok'45'all_506 v2 v3))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_574 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 ->
  T_SegOK_490 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_574 = erased
-- Once.CCC.Codegen.SlotSeg.segok-weaken
d_segok'45'weaken_584 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_490 -> T_SegOK_490
d_segok'45'weaken_584 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_512
      (\ v5 ->
         coe
           d_seg'45'weaken'45'cur_358 v0 v1 v5 v2 v3
           (coe d_ok'45'all_506 v4 v5))
-- Once.CCC.Codegen.SlotSeg.segok-pre
d_segok'45'pre_596 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_490 -> T_SegOK_490
d_segok'45'pre_596 ~v0 v1 ~v2 ~v3 v4 v5
  = du_segok'45'pre_596 v1 v4 v5
du_segok'45'pre_596 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_490 -> T_SegOK_490
du_segok'45'pre_596 v0 v1 v2
  = coe
      du_segok'45''43''43'_556 (coe v0)
      (coe du_segok'45'idle_518 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotSeg.segok-thunk
d_segok'45'thunk_616 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490
d_segok'45'thunk_616 v0 ~v1 ~v2 ~v3 v4 v5
  = du_segok'45'thunk_616 v0 v4 v5
du_segok'45'thunk_616 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490
du_segok'45'thunk_616 v0 v1 v2
  = coe C_mkSegOK_512 (coe du_inner_636 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_636 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> [Integer] -> T_AllSeg_200
d_inner_636 v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inner_636 v0 v4 v5 v6
du_inner_636 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> [Integer] -> T_AllSeg_200
du_inner_636 v0 v1 v2 v3
  = coe
      C__'8759'__212 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_220 (coe v1)
         (coe
            d_ok'45'all_506 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__212 (coe du_sb'45'none_40)
            (coe C__'8759'__212 (coe du_sb'45'none_40) (coe C_'91''93'_204))))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_644 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_644 = erased
-- Once.CCC.Codegen.SlotSeg.segok-block
d_segok'45'block_656 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490
d_segok'45'block_656 v0 ~v1 ~v2 v3 v4
  = du_segok'45'block_656 v0 v3 v4
du_segok'45'block_656 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> T_SegOK_490
du_segok'45'block_656 v0 v1 v2
  = coe C_mkSegOK_512 (coe du_inner_674 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_674 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> [Integer] -> T_AllSeg_200
d_inner_674 v0 ~v1 ~v2 v3 v4 v5 = du_inner_674 v0 v3 v4 v5
du_inner_674 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 -> [Integer] -> T_AllSeg_200
du_inner_674 v0 v1 v2 v3
  = coe
      C__'8759'__212 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_220 (coe v1)
         (coe
            d_ok'45'all_506 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe C__'8759'__212 (coe du_sb'45'none_40) (coe C_'91''93'_204)))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_682 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_SegOK_490 ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_682 = erased
-- Once.CCC.Codegen.SlotSeg.BlockOK
d_BlockOK_686 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockOK_686 = erased
-- Once.CCC.Codegen.SlotSeg.segok-blocks
d_segok'45'blocks_696 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_490
d_segok'45'blocks_696 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe
                du_segok'45'idle_518 (coe v1)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v2 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                             -> coe
                                  du_segok'45''43''43'_556
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                                           (coe
                                              MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v5))
                                           (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238
                                                 (coe v7)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                  (coe du_segok'45'block_656 (coe v0) (coe v8) (coe v11))
                                  (coe d_segok'45'blocks_696 (coe v0) (coe v4) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.trace-lookup
d_trace'45'lookup_710 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_trace'45'lookup_710 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_trace'45'lookup_710 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.fetch-at
d_fetch'45'at_718 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_fetch'45'at_718 = coe d_trace'45'lookup_710
-- Once.CCC.Codegen.SlotSeg.seg-at
d_seg'45'at_720 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> T_SegState_120 -> T_SegState_120
d_seg'45'at_720 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       d_seg'45'at_720 (coe v5) (coe v3)
                       (coe d_seg'45'step_164 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotSeg.seg-at-suc
d_seg'45'at'45'suc_742 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_SegState_120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_742 = erased
-- Once.CCC.Codegen.SlotSeg.idle-seg-at
d_idle'45'seg'45'at_770 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_770 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_804 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  T_SegState_120 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_804 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_840 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  T_SegState_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_840 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ˡ
d_fetch'45''43''43''737'_864 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_864 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ʳ
d_fetch'45''43''43''691'_892 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_892 = erased
-- Once.CCC.Codegen.SlotSeg.split-pos
d_split'45'pos_912 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_912 v0 v1
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
                    (let v5 = d_split'45'pos_912 (coe v3) (coe v4) in
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
-- Once.CCC.Codegen.SlotSeg.allseg-at
d_allseg'45'at_956 ::
  T_SegState_120 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_AllSeg_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_12
d_allseg'45'at_956 ~v0 v1 v2 ~v3 v4 ~v5
  = du_allseg'45'at_956 v1 v2 v4
du_allseg'45'at_956 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> T_AllSeg_200 -> T_SlotBelow_12
du_allseg'45'at_956 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__212 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__212 v9 v10
                         -> coe du_allseg'45'at_956 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
