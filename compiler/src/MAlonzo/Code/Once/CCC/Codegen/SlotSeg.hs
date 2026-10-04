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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sb'45'weaken_106 ~v0 ~v1 v2 v3 v4 = du_sb'45'weaken_106 v2 v3 v4
du_sb'45'weaken_106 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_SegAction_156
d_seg'45'action_164 v0
  = let v1 = coe C_seg'45'id_158 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224 v3 v4
                  -> coe C_seg'45'push_160 (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226 v3
                  -> coe C_seg'45'pop_162
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2230 v3
                  -> coe C_seg'45'push_160 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.SlotSeg.pop-with
d_pop'45'with_170 :: [Integer] -> T_SegState_144 -> T_SegState_144
d_pop'45'with_170 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe C_mkSeg_154 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply
d_seg'45'apply_178 ::
  T_SegAction_156 -> T_SegState_144 -> T_SegState_144
d_seg'45'apply_178 v0 v1
  = case coe v0 of
      C_seg'45'id_158 -> coe v1
      C_seg'45'push_160 v2
        -> coe
             C_mkSeg_154 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_cur_150 (coe v1)) (coe d_saved_152 (coe v1)))
      C_seg'45'pop_162
        -> coe d_pop'45'with_170 (coe d_saved_152 (coe v1)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-step
d_seg'45'step_188 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_SegState_144 -> T_SegState_144
d_seg'45'step_188 v0 v1
  = coe
      d_seg'45'apply_178 (coe d_seg'45'action_164 (coe v0)) (coe v1)
-- Once.CCC.Codegen.SlotSeg.seg-fold
d_seg'45'fold_194 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegState_144 -> T_SegState_144
d_seg'45'fold_194 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_seg'45'fold_194 (coe v3)
             (coe d_seg'45'step_188 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-fold-++
d_seg'45'fold'45''43''43'_210 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'fold'45''43''43'_210 = erased
-- Once.CCC.Codegen.SlotSeg.AllSeg
d_AllSeg_224 a0 a1 = ()
data T_AllSeg_224
  = C_'91''93'_228 | C__'8759'__236 T_SlotBelow_12 T_AllSeg_224
-- Once.CCC.Codegen.SlotSeg.allseg-++
d_allseg'45''43''43'_244 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_AllSeg_224 -> T_AllSeg_224 -> T_AllSeg_224
d_allseg'45''43''43'_244 ~v0 v1 ~v2 v3 v4
  = du_allseg'45''43''43'_244 v1 v3 v4
du_allseg'45''43''43'_244 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_AllSeg_224 -> T_AllSeg_224 -> T_AllSeg_224
du_allseg'45''43''43'_244 v0 v1 v2
  = case coe v1 of
      C_'91''93'_228 -> coe v2
      C__'8759'__236 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C__'8759'__236 v6
                    (coe du_allseg'45''43''43'_244 (coe v9) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.allseg-++bal
d_allseg'45''43''43'bal_260 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllSeg_224 -> T_AllSeg_224 -> T_AllSeg_224
d_allseg'45''43''43'bal_260 ~v0 v1 ~v2 ~v3 v4 v5
  = du_allseg'45''43''43'bal_260 v1 v4 v5
du_allseg'45''43''43'bal_260 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_AllSeg_224 -> T_AllSeg_224 -> T_AllSeg_224
du_allseg'45''43''43'bal_260 v0 v1 v2
  = coe du_allseg'45''43''43'_244 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.SlotSeg.SavedLE
d_SavedLE_270 a0 a1 = ()
data T_SavedLE_270
  = C_'91''93'_272 |
    C__'8759'__282 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                   T_SavedLE_270
-- Once.CCC.Codegen.SlotSeg.SegLE
d_SegLE_288 a0 a1 = ()
data T_SegLE_288
  = C_mkSegLE_302 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                  T_SavedLE_270
-- Once.CCC.Codegen.SlotSeg.SegLE.cur-le
d_cur'45'le_298 ::
  T_SegLE_288 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cur'45'le_298 v0
  = case coe v0 of
      C_mkSegLE_302 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegLE.saved-le
d_saved'45'le_300 :: T_SegLE_288 -> T_SavedLE_270
d_saved'45'le_300 v0
  = case coe v0 of
      C_mkSegLE_302 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.saved-le-refl
d_saved'45'le'45'refl_306 :: [Integer] -> T_SavedLE_270
d_saved'45'le'45'refl_306 v0
  = case coe v0 of
      [] -> coe C_'91''93'_272
      (:) v1 v2
        -> coe
             C__'8759'__282
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
             (d_saved'45'le'45'refl_306 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.pop-mono
d_pop'45'mono_320 ::
  T_SegState_144 ->
  T_SegState_144 ->
  [Integer] ->
  [Integer] -> T_SavedLE_270 -> T_SegLE_288 -> T_SegLE_288
d_pop'45'mono_320 ~v0 ~v1 v2 v3 v4 v5
  = du_pop'45'mono_320 v2 v3 v4 v5
du_pop'45'mono_320 ::
  [Integer] ->
  [Integer] -> T_SavedLE_270 -> T_SegLE_288 -> T_SegLE_288
du_pop'45'mono_320 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v3)
      (:) v4 v5
        -> coe
             seq (coe v1)
             (case coe v2 of
                C__'8759'__282 v10 v11 -> coe C_mkSegLE_302 (coe v10) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-apply-mono
d_seg'45'apply'45'mono_342 ::
  T_SegAction_156 ->
  T_SegState_144 -> T_SegState_144 -> T_SegLE_288 -> T_SegLE_288
d_seg'45'apply'45'mono_342 v0 v1 v2 v3
  = case coe v0 of
      C_seg'45'id_158 -> coe v3
      C_seg'45'push_160 v4
        -> coe
             C_mkSegLE_302
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe d_cur_150 (coe d_seg'45'apply_178 (coe v0) (coe v1))))
             (coe
                C__'8759'__282 (d_cur'45'le_298 (coe v3))
                (d_saved'45'le_300 (coe v3)))
      C_seg'45'pop_162
        -> coe
             du_pop'45'mono_320 (coe d_saved_152 (coe v1))
             (coe d_saved_152 (coe v2)) (coe d_saved'45'le_300 (coe v3))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken
d_seg'45'weaken_362 ::
  T_SegState_144 ->
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegLE_288 -> T_AllSeg_224 -> T_AllSeg_224
d_seg'45'weaken_362 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_228 -> coe C_'91''93'_228
      C__'8759'__236 v8 v9
        -> case coe v2 of
             (:) v10 v11
               -> coe
                    C__'8759'__236
                    (coe du_sb'45'le_130 (coe d_cur'45'le_298 (coe v3)) (coe v8))
                    (d_seg'45'weaken_362
                       (coe
                          d_seg'45'apply_178 (coe d_seg'45'action_164 (coe v10)) (coe v0))
                       (coe d_seg'45'step_188 (coe v10) (coe v1)) (coe v11)
                       (coe
                          d_seg'45'apply'45'mono_342 (coe d_seg'45'action_164 (coe v10))
                          (coe v0) (coe v1) (coe v3))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-weaken-cur
d_seg'45'weaken'45'cur_382 ::
  Integer ->
  Integer ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_AllSeg_224 -> T_AllSeg_224
d_seg'45'weaken'45'cur_382 v0 v1 v2 v3 v4
  = coe
      d_seg'45'weaken_362 (coe C_mkSeg_154 (coe v0) (coe v2))
      (coe C_mkSeg_154 (coe v1) (coe v2)) (coe v3)
      (coe
         C_mkSegLE_302 (coe v4) (coe d_saved'45'le'45'refl_306 (coe v2)))
-- Once.CCC.Codegen.SlotSeg.is-id?
d_is'45'id'63'_388 :: T_SegAction_156 -> Bool
d_is'45'id'63'_388 v0
  = case coe v0 of
      C_seg'45'id_158 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_seg'45'push_160 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_seg'45'pop_162 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.seg-idle?
d_seg'45'idle'63'_390 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> Bool
d_seg'45'idle'63'_390 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is'45'id'63'_388 (coe d_seg'45'action_164 (coe v1)))
             (coe d_seg'45'idle'63'_390 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.idle-step
d_idle'45'step_400 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'step_400 = erased
-- Once.CCC.Codegen.SlotSeg._.go
d_go_414 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 ->
  T_SegAction_156 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_414 = erased
-- Once.CCC.Codegen.SlotSeg.idle-head
d_idle'45'head_420 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'head_420 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-fst
d_'8743''45'fst_436 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'fst_436 = erased
-- Once.CCC.Codegen.SlotSeg.idle-tail
d_idle'45'tail_446 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'tail_446 = erased
-- Once.CCC.Codegen.SlotSeg._.∧-snd
d_'8743''45'snd_462 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'snd_462 = erased
-- Once.CCC.Codegen.SlotSeg.idle-++
d_idle'45''43''43'_474 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45''43''43'_474 = erased
-- Once.CCC.Codegen.SlotSeg.idle-neutral
d_idle'45'neutral_498 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'neutral_498 = erased
-- Once.CCC.Codegen.SlotSeg.SegOK
d_SegOK_514 a0 a1 = ()
newtype T_SegOK_514 = C_mkSegOK_536 ([Integer] -> T_AllSeg_224)
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-all
d_ok'45'all_530 :: T_SegOK_514 -> [Integer] -> T_AllSeg_224
d_ok'45'all_530 v0
  = case coe v0 of
      C_mkSegOK_536 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.SegOK.ok-neu
d_ok'45'neu_534 ::
  T_SegOK_514 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'neu_534 = erased
-- Once.CCC.Codegen.SlotSeg.segok-idle
d_segok'45'idle_542 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_514
d_segok'45'idle_542 ~v0 v1 ~v2 v3 = du_segok'45'idle_542 v1 v3
du_segok'45'idle_542 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_514
du_segok'45'idle_542 v0 v1
  = coe C_mkSegOK_536 (\ v2 -> coe du_go_558 (coe v0) (coe v1))
-- Once.CCC.Codegen.SlotSeg._.go
d_go_558 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [Integer] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_224
d_go_558 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_go_558 v5 v7
du_go_558 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_AllSeg_224
du_go_558 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe C_'91''93'_228)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe C__'8759'__236 v6 (coe du_go_558 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.segok-++
d_segok'45''43''43'_580 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514 -> T_SegOK_514
d_segok'45''43''43'_580 ~v0 v1 ~v2 v3 v4
  = du_segok'45''43''43'_580 v1 v3 v4
du_segok'45''43''43'_580 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514 -> T_SegOK_514
du_segok'45''43''43'_580 v0 v1 v2
  = coe
      C_mkSegOK_536
      (\ v3 ->
         coe
           du_allseg'45''43''43'bal_260 (coe v0) (coe d_ok'45'all_530 v1 v3)
           (coe d_ok'45'all_530 v2 v3))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_598 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 ->
  T_SegOK_514 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_598 = erased
-- Once.CCC.Codegen.SlotSeg.segok-weaken
d_segok'45'weaken_608 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SegOK_514 -> T_SegOK_514
d_segok'45'weaken_608 v0 v1 v2 v3 v4
  = coe
      C_mkSegOK_536
      (\ v5 ->
         coe
           d_seg'45'weaken'45'cur_382 v0 v1 v5 v2 v3
           (coe d_ok'45'all_530 v4 v5))
-- Once.CCC.Codegen.SlotSeg.segok-pre
d_segok'45'pre_620 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_514 -> T_SegOK_514
d_segok'45'pre_620 ~v0 v1 ~v2 ~v3 v4 v5
  = du_segok'45'pre_620 v1 v4 v5
du_segok'45'pre_620 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_SegOK_514 -> T_SegOK_514
du_segok'45'pre_620 v0 v1 v2
  = coe
      du_segok'45''43''43'_580 (coe v0)
      (coe du_segok'45'idle_542 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Codegen.SlotSeg.segok-thunk
d_segok'45'thunk_640 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514
d_segok'45'thunk_640 v0 ~v1 ~v2 ~v3 v4 v5
  = du_segok'45'thunk_640 v0 v4 v5
du_segok'45'thunk_640 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514
du_segok'45'thunk_640 v0 v1 v2
  = coe C_mkSegOK_536 (coe du_inner_660 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_660 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> [Integer] -> T_AllSeg_224
d_inner_660 v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inner_660 v0 v4 v5 v6
du_inner_660 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> [Integer] -> T_AllSeg_224
du_inner_660 v0 v1 v2 v3
  = coe
      C__'8759'__236 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_244 (coe v1)
         (coe
            d_ok'45'all_530 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe
            C__'8759'__236 (coe du_sb'45'none_40)
            (coe C__'8759'__236 (coe du_sb'45'none_40) (coe C_'91''93'_228))))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_668 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_668 = erased
-- Once.CCC.Codegen.SlotSeg.segok-block
d_segok'45'block_680 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514
d_segok'45'block_680 v0 ~v1 ~v2 v3 v4
  = du_segok'45'block_680 v0 v3 v4
du_segok'45'block_680 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> T_SegOK_514
du_segok'45'block_680 v0 v1 v2
  = coe C_mkSegOK_536 (coe du_inner_698 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.SlotSeg._.inner
d_inner_698 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> [Integer] -> T_AllSeg_224
d_inner_698 v0 ~v1 ~v2 v3 v4 v5 = du_inner_698 v0 v3 v4 v5
du_inner_698 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 -> [Integer] -> T_AllSeg_224
du_inner_698 v0 v1 v2 v3
  = coe
      C__'8759'__236 (coe du_sb'45'none_40)
      (coe
         du_allseg'45''43''43'_244 (coe v1)
         (coe
            d_ok'45'all_530 v2
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
         (coe C__'8759'__236 (coe du_sb'45'none_40) (coe C_'91''93'_228)))
-- Once.CCC.Codegen.SlotSeg._.neu
d_neu_706 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SegOK_514 ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neu_706 = erased
-- Once.CCC.Codegen.SlotSeg.BlockOK
d_BlockOK_710 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockOK_710 = erased
-- Once.CCC.Codegen.SlotSeg.segok-blocks
d_segok'45'blocks_720 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_SegOK_514
d_segok'45'blocks_720 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe
                du_segok'45'idle_542 (coe v1)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v2 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                             -> coe
                                  du_segok'45''43''43'_580
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
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
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226
                                                 (coe v7)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                  (coe du_segok'45'block_680 (coe v0) (coe v8) (coe v11))
                                  (coe d_segok'45'blocks_720 (coe v0) (coe v4) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.trace-lookup
d_trace'45'lookup_734 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_trace'45'lookup_734 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_trace'45'lookup_734 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.SlotSeg.fetch-at
d_fetch'45'at_742 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch'45'at_742 = coe d_trace'45'lookup_734
-- Once.CCC.Codegen.SlotSeg.seg-at
d_seg'45'at_744 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> T_SegState_144 -> T_SegState_144
d_seg'45'at_744 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe v2
                (:) v4 v5
                  -> coe
                       d_seg'45'at_744 (coe v5) (coe v3)
                       (coe d_seg'45'step_188 (coe v4) (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.SlotSeg.seg-at-suc
d_seg'45'at'45'suc_766 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45'suc_766 = erased
-- Once.CCC.Codegen.SlotSeg.idle-seg-at
d_idle'45'seg'45'at_794 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idle'45'seg'45'at_794 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ˡ
d_seg'45'at'45''43''43''737'_828 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  T_SegState_144 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''737'_828 = erased
-- Once.CCC.Codegen.SlotSeg.seg-at-++ʳ
d_seg'45'at'45''43''43''691'_864 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  T_SegState_144 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'at'45''43''43''691'_864 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ˡ
d_fetch'45''43''43''737'_888 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''737'_888 = erased
-- Once.CCC.Codegen.SlotSeg.fetch-++ʳ
d_fetch'45''43''43''691'_916 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''691'_916 = erased
-- Once.CCC.Codegen.SlotSeg.split-pos
d_split'45'pos_936 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split'45'pos_936 v0 v1
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
                    (let v5 = d_split'45'pos_936 (coe v3) (coe v4) in
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
d_allseg'45'at_980 ::
  T_SegState_144 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_AllSeg_224 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SlotBelow_12
d_allseg'45'at_980 ~v0 v1 v2 ~v3 v4 ~v5
  = du_allseg'45'at_980 v1 v2 v4
du_allseg'45'at_980 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> T_AllSeg_224 -> T_SlotBelow_12
du_allseg'45'at_980 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    C__'8759'__236 v8 v9 -> coe v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       C__'8759'__236 v9 v10
                         -> coe du_allseg'45'at_980 (coe v4) (coe v5) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
