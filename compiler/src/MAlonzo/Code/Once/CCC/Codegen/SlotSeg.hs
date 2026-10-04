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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
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
-- Once.CCC.Codegen.SlotSeg.sb-weaken
d_sb'45'weaken_106 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_106 ~v0 ~v1 v2 v3 v4 = du_sb'45'weaken_106 v2 v3 v4
du_sb'45'weaken_106 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sb'45'weaken_106 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       C_mkSlotBelow_34
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_below_28 v5 v9 erased) (coe v1)))
                       (coe
                          (\ v9 v10 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                               (coe d_pair'45'below_32 v5 v9 erased) (coe v1))))
                    (coe du_sb'45'weaken_106 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.sb-le
d_sb'45'le_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_12 -> T_SlotBelow_12
d_sb'45'le_130 ~v0 ~v1 ~v2 v3 v4 = du_sb'45'le_130 v3 v4
du_sb'45'le_130 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SlotBelow_12 -> T_SlotBelow_12
du_sb'45'le_130 v0 v1
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
d_SegState_144 = ()
data T_SegState_144 = C_mkSeg_154 Integer [Integer]
-- Once.CCC.Codegen.SlotSeg.SegState.cur
d_cur_150 :: T_SegState_144 -> Integer
d_cur_150 v0
  = case coe v0 of
      C_mkSeg_154 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegState.saved
d_saved_152 :: T_SegState_144 -> [Integer]
d_saved_152 v0
  = case coe v0 of
      C_mkSeg_154 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegAction
d_SegAction_156 = ()
data T_SegAction_156
  = C_seg'45'id_158 | C_seg'45'push_160 Integer | C_seg'45'pop_162
-- Once.CCC.Codegen.SlotSeg.seg-action
d_seg'45'action_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  T_SegAction_156
d_seg'45'action_164 v0
  = let v1 = coe C_seg'45'id_158 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224 v3 v4
                  -> coe C_seg'45'push_160 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226 v3
                  -> coe C_seg'45'pop_162
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotSeg.pop-with
d_pop'45'with_168 :: [Integer] -> T_SegState_144 -> T_SegState_144
d_pop'45'with_168 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_154 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply
d_seg'45'apply_176 ::
  T_SegAction_156 -> T_SegState_144 -> T_SegState_144
d_seg'45'apply_176 v0 v1
  = case coe v0 of
      C_seg'45'id_158 -> coe v1
      C_seg'45'push_160 v2
        -> coe
             C_mkSeg_154 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_150 (coe v1)) (coe d_saved_152 (coe v1)))
      C_seg'45'pop_162
        -> coe d_pop'45'with_168 (coe d_saved_152 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-step
d_seg'45'step_186 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  T_SegState_144 -> T_SegState_144
d_seg'45'step_186 v0 v1
  = coe
      d_seg'45'apply_176 (coe d_seg'45'action_164 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotSeg.seg-fold
d_seg'45'fold_192 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegState_144 -> T_SegState_144
d_seg'45'fold_192 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_seg'45'fold_192 (coe v3)
             (coe d_seg'45'step_186 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-fold-++
d_seg'45'fold'45''43''43'_208 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_208 = erased
-- Once.CCC.Codegen.SlotSeg.AllSeg
d_AllSeg_222 a0 a1 = ()
data T_AllSeg_222
  = C_'91''93'_226 | C__'8759'__234 T_SlotBelow_12 T_AllSeg_222
-- Once.CCC.Codegen.SlotSeg.allseg-++
d_allseg'45''43''43'_242 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_AllSeg_222 -> T_AllSeg_222 -> T_AllSeg_222
d_allseg'45''43''43'_242 ~v0 v1 ~v2 v3 v4
  = du_allseg'45''43''43'_242 v1 v3 v4
du_allseg'45''43''43'_242 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_AllSeg_222 -> T_AllSeg_222 -> T_AllSeg_222
du_allseg'45''43''43'_242 v0 v1 v2
  = case coe v1 of
      C_'91''93'_226 -> coe v2
      C__'8759'__234 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__234 v6
                    (coe du_allseg'45''43''43'_242 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.allseg-++bal
d_allseg'45''43''43'bal_258 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_222 -> T_AllSeg_222 -> T_AllSeg_222
d_allseg'45''43''43'bal_258 ~v0 v1 ~v2 ~v3 v4 v5
  = du_allseg'45''43''43'bal_258 v1 v4 v5
du_allseg'45''43''43'bal_258 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_AllSeg_222 -> T_AllSeg_222 -> T_AllSeg_222
du_allseg'45''43''43'bal_258 v0 v1 v2
  = coe du_allseg'45''43''43'_242 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotSeg.SavedLE
d_SavedLE_268 a0 a1 = ()
data T_SavedLE_268
  = C_'91''93'_270 |
    C__'8759'__280 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_268
-- Once.CCC.Codegen.SlotSeg.SegLE
d_SegLE_286 a0 a1 = ()
data T_SegLE_286
  = C_mkSegLE_300 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_268
-- Once.CCC.Codegen.SlotSeg.SegLE.cur-le
d_cur'45'le_296 ::
  T_SegLE_286 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_296 v0
  = case coe v0 of
      C_mkSegLE_300 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegLE.saved-le
d_saved'45'le_298 :: T_SegLE_286 -> T_SavedLE_268
d_saved'45'le_298 v0
  = case coe v0 of
      C_mkSegLE_300 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.saved-le-refl
d_saved'45'le'45'refl_304 :: [Integer] -> T_SavedLE_268
d_saved'45'le'45'refl_304 v0
  = case coe v0 of
      [] -> coe C_'91''93'_270
      (:) v1 v2
        -> coe
             C__'8759'__280
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (d_saved'45'le'45'refl_304 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.pop-mono
d_pop'45'mono_318 ::
  T_SegState_144 ->
  T_SegState_144 ->
  [Integer] ->
  [Integer] -> T_SavedLE_268 -> T_SegLE_286 -> T_SegLE_286
d_pop'45'mono_318 ~v0 ~v1 v2 v3 v4 v5
  = du_pop'45'mono_318 v2 v3 v4 v5
du_pop'45'mono_318 ::
  [Integer] ->
  [Integer] -> T_SavedLE_268 -> T_SegLE_286 -> T_SegLE_286
du_pop'45'mono_318 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__280 v10 v11 -> coe C_mkSegLE_300 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply-mono
d_seg'45'apply'45'mono_340 ::
  T_SegAction_156 ->
  T_SegState_144 -> T_SegState_144 -> T_SegLE_286 -> T_SegLE_286
d_seg'45'apply'45'mono_340 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_158 -> coe v3
      C_seg'45'push_160 v4
        -> coe
             C_mkSegLE_300
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_150 (coe d_seg'45'apply_176 (coe v0) (coe v1))))
             (coe
                C__'8759'__280 (d_cur'45'le_296 (coe v3))
                (d_saved'45'le_298 (coe v3)))
      C_seg'45'pop_162
        -> coe
             du_pop'45'mono_318 (coe d_saved_152 (coe v1))
             (coe d_saved_152 (coe v2)) (coe d_saved'45'le_298 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken
d_seg'45'weaken_360 ::
  T_SegState_144 ->
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegLE_286 -> T_AllSeg_222 -> T_AllSeg_222
d_seg'45'weaken_360 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_226 -> coe C_'91''93'_226
      C__'8759'__234 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__234
                    (coe du_sb'45'le_130 (coe d_cur'45'le_296 (coe v3)) (coe v8))
                    (d_seg'45'weaken_360
                       (coe
                          d_seg'45'apply_176 (coe d_seg'45'action_164 (coe v10)) (coe v0))
                       (coe d_seg'45'step_186 (coe v10) (coe v1)) (coe v11)
                       (coe
                          d_seg'45'apply'45'mono_340 (coe d_seg'45'action_164 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken-cur
d_seg'45'weaken'45'cur_380 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_222 -> T_AllSeg_222
d_seg'45'weaken'45'cur_380 v0 v1 v2 v3 v4
  = coe
      d_seg'45'weaken_360 (coe C_mkSeg_154 (coe v0) (coe v2))
      (coe C_mkSeg_154 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_300 (coe v4) (coe d_saved'45'le'45'refl_304 (coe v2)))
-- Once.CCC.Codegen.SlotSeg.is-id?
d_is'45'id'63'_386 :: T_SegAction_156 -> Bool
d_is'45'id'63'_386 v0
  = case coe v0 of
      C_seg'45'id_158 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_160 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_162 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-idle?
d_seg'45'idle'63'_388 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] -> Bool
d_seg'45'idle'63'_388 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is'45'id'63'_386 (coe d_seg'45'action_164 (coe v1)))
             (coe d_seg'45'idle'63'_388 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.idle-step
d_idle'45'step_398 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_398 = erased
-- Once.CCC.Codegen.SlotSeg._.go
d_go_412 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 ->
  T_SegAction_156 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_412 = erased
-- Once.CCC.Codegen.SlotSeg.idle-head
d_idle'45'head_418 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_418 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-fst
d_'8743''45'fst_434 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_434 = erased
-- Once.CCC.Codegen.SlotSeg.idle-tail
d_idle'45'tail_444 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_444 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-snd
d_'8743''45'snd_460 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_460 = erased
-- Once.CCC.Codegen.SlotSeg.idle-++
d_idle'45''43''43'_472 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_472 = erased
-- Once.CCC.Codegen.SlotSeg.idle-neutral
d_idle'45'neutral_496 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_496 = erased
-- Once.CCC.Codegen.SlotSeg.SegOK
d_SegOK_512 a0 a1 = ()
newtype T_SegOK_512 = C_mkSegOK_534 ([Integer] -> T_AllSeg_222)
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-all
d_ok'45'all_528 :: T_SegOK_512 -> [Integer] -> T_AllSeg_222
d_ok'45'all_528 v0
  = case coe v0 of
      C_mkSegOK_534 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-neu
d_ok'45'neu_532 ::
  T_SegOK_512 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_532 = erased
-- Once.CCC.Codegen.SlotSeg.segok-idle
d_segok'45'idle_540 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_512
d_segok'45'idle_540 ~v0 v1 ~v2 v3 = du_segok'45'idle_540 v1 v3
du_segok'45'idle_540 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_512
du_segok'45'idle_540 v0 v1
  = coe C_mkSegOK_534 (\ v2 -> coe du_go_556 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotSeg._.go
d_go_556 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_222
d_go_556 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_go_556 v5 v7
du_go_556 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_222
du_go_556 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_226)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__234 v6 (coe du_go_556 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.segok-++
d_segok'45''43''43'_578 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512 -> T_SegOK_512
d_segok'45''43''43'_578 ~v0 v1 ~v2 v3 v4
  = du_segok'45''43''43'_578 v1 v3 v4
du_segok'45''43''43'_578 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512 -> T_SegOK_512
du_segok'45''43''43'_578 v0 v1 v2
  = coe
      C_mkSegOK_534
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_258 (coe v0) (coe d_ok'45'all_528 v1 v3)
           (coe d_ok'45'all_528 v2 v3))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_596 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 ->
  T_SegOK_512 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_596 = erased
-- Once.CCC.Codegen.SlotSeg.segok-weaken
d_segok'45'weaken_606 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_512 -> T_SegOK_512
d_segok'45'weaken_606 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_534
      (\ v5 ->
         coe
           d_seg'45'weaken'45'cur_380 v0 v1 v5 v2 v3
           (coe d_ok'45'all_528 v4 v5))
-- Once.CCC.Codegen.SlotSeg.segok-pre
d_segok'45'pre_618 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_512 -> T_SegOK_512
d_segok'45'pre_618 ~v0 v1 ~v2 ~v3 v4 v5
  = du_segok'45'pre_618 v1 v4 v5
du_segok'45'pre_618 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_512 -> T_SegOK_512
du_segok'45'pre_618 v0 v1 v2
  = coe
      du_segok'45''43''43'_578 (coe v0)
      (coe du_segok'45'idle_540 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotSeg.segok-thunk
d_segok'45'thunk_638 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512
d_segok'45'thunk_638 v0 ~v1 ~v2 ~v3 v4 v5
  = du_segok'45'thunk_638 v0 v4 v5
du_segok'45'thunk_638 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512
du_segok'45'thunk_638 v0 v1 v2
  = coe C_mkSegOK_534 (coe du_inner_658 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_658 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> [Integer] -> T_AllSeg_222
d_inner_658 v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inner_658 v0 v4 v5 v6
du_inner_658 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> [Integer] -> T_AllSeg_222
du_inner_658 v0 v1 v2 v3
  = coe
      C__'8759'__234 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_242 (coe v1)
         (coe
            d_ok'45'all_528 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__234 (coe du_sb'45'none_40)
            (coe C__'8759'__234 (coe du_sb'45'none_40) (coe C_'91''93'_226))))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_666 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_666 = erased
-- Once.CCC.Codegen.SlotSeg.segok-block
d_segok'45'block_678 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512
d_segok'45'block_678 v0 ~v1 ~v2 v3 v4
  = du_segok'45'block_678 v0 v3 v4
du_segok'45'block_678 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> T_SegOK_512
du_segok'45'block_678 v0 v1 v2
  = coe C_mkSegOK_534 (coe du_inner_696 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_696 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> [Integer] -> T_AllSeg_222
d_inner_696 v0 ~v1 ~v2 v3 v4 v5 = du_inner_696 v0 v3 v4 v5
du_inner_696 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 -> [Integer] -> T_AllSeg_222
du_inner_696 v0 v1 v2 v3
  = coe
      C__'8759'__234 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_242 (coe v1)
         (coe
            d_ok'45'all_528 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe C__'8759'__234 (coe du_sb'45'none_40) (coe C_'91''93'_226)))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_704 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_SegOK_512 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_704 = erased
-- Once.CCC.Codegen.SlotSeg.BlockOK
d_BlockOK_708 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockOK_708 = erased
-- Once.CCC.Codegen.SlotSeg.segok-blocks
d_segok'45'blocks_718 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_512
d_segok'45'blocks_718 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe
                du_segok'45'idle_540 (coe v1)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v2 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                             -> coe
                                  du_segok'45''43''43'_578
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224
                                           (coe
                                              MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v5))
                                           (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226
                                                 (coe v7)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                  (coe du_segok'45'block_678 (coe v0) (coe v8) (coe v11))
                                  (coe d_segok'45'blocks_718 (coe v0) (coe v4) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.trace-lookup
d_trace'45'lookup_732 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236
d_trace'45'lookup_732 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_trace'45'lookup_732 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.fetch-at
d_fetch'45'at_740 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236
d_fetch'45'at_740 = coe d_trace'45'lookup_732
-- Once.CCC.Codegen.SlotSeg.seg-at
d_seg'45'at_742 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer -> T_SegState_144 -> T_SegState_144
d_seg'45'at_742 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       d_seg'45'at_742 (coe v5) (coe v3)
                       (coe d_seg'45'step_186 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotSeg.seg-at-suc
d_seg'45'at'45'suc_764 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_764 = erased
-- Once.CCC.Codegen.SlotSeg.idle-seg-at
d_idle'45'seg'45'at_792 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_792 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_826 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  T_SegState_144 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_826 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_862 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_862 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ˡ
d_fetch'45''43''43''737'_886 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_886 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ʳ
d_fetch'45''43''43''691'_914 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_914 = erased
-- Once.CCC.Codegen.SlotSeg.split-pos
d_split'45'pos_934 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_934 v0 v1
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
                    (let v5 = d_split'45'pos_934 (coe v3) (coe v4) in
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
d_allseg'45'at_978 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  T_AllSeg_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_12
d_allseg'45'at_978 ~v0 v1 v2 ~v3 v4 ~v5
  = du_allseg'45'at_978 v1 v2 v4
du_allseg'45'at_978 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer -> T_AllSeg_222 -> T_SlotBelow_12
du_allseg'45'at_978 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__234 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__234 v9 v10
                         -> coe du_allseg'45'at_978 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
