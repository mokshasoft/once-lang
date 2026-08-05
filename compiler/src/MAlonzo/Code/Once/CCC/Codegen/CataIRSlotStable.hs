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

module MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.AllSlotStable
d_AllSlotStable_14 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_AllSlotStable_14 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStable
d_SlotStable_16 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_SlotStable_16 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStableT
d_SlotStableT_18 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_SlotStableT_18 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.trc
d_trc_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_trc_24 ~v0 v1 = du_trc_24 v1
du_trc_24 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_trc_24 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.All→AllI
d_All'8594'AllI_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_30 ~v0 v1 v2 = du_All'8594'AllI_30 v1 v2
du_All'8594'AllI_30 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_30 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe du_All'8594'AllI_30 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?
d_stable'63'_36 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> Bool
d_stable'63'_36 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_all'45'stable'63'_38 (coe v0) (coe v3))
                (coe d_all'45'stable'63'_38 (coe v0) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v2)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?
d_all'45'stable'63'_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> Bool
d_all'45'stable'63'_38 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_stable'63'_36 (coe v0) (coe v2))
             (coe d_all'45'stable'63'_38 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-split
d_'8743''45'split_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_52 ~v0 v1 v2 ~v3 = du_'8743''45'split_52 v1 v2
du_'8743''45'split_52 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_52 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_56 v0 v1 ~v2
  = du_stable'63''45'sound_56 v0 v1
du_stable'63''45'sound_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny
du_stable'63''45'sound_56 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_All'8594'AllI_30 (coe v2)
                (coe du_all'45'stable'63''45'sound_60 (coe v0) (coe v2)))
             (coe
                du_All'8594'AllI_30 (coe v3)
                (coe du_all'45'stable'63''45'sound_60 (coe v0) (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_60 v0 v1 ~v2
  = du_all'45'stable'63''45'sound_60 v0 v1
du_all'45'stable'63''45'sound_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_60 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_stable'63''45'sound_56 (coe v0) (coe v2))
             (coe du_all'45'stable'63''45'sound_60 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.AllI→All
d_AllI'8594'All_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_84 ~v0 v1 v2 = du_AllI'8594'All_84 v1 v2
du_AllI'8594'All_84 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_84 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (coe du_AllI'8594'All_84 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-intro
d_'8743''45'intro_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_94 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_110 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_124 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_128 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_158 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Type.C_K_114 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
      MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                         (coe v1) (coe v2) (coe v3) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v7)))
                            (coe v6)))
                      (coe
                         d_visit'45'walk'45'stable_158 (coe v0) (coe v1) (coe v2) (coe v3)
                         (coe v8) (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v7)))
                            (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                                        (coe v1) (coe v2) (coe v3) (coe v7)
                                        (coe addInt (coe (4 :: Integer)) (coe v5))
                                        (coe addInt (coe (2 :: Integer)) (coe v6)))
                                     (coe
                                        d_visit'45'walk'45'stable_158 (coe v0) (coe v1) (coe v2)
                                        (coe v3) (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5))
                                        (coe addInt (coe (2 :: Integer)) (coe v6)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_180
                            (coe v1) (coe v2) (coe v3) (coe v8)
                            (coe addInt (coe (4 :: Integer)) (coe v5))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v7))
                               (coe v6)))
                         (coe
                            d_visit'45'walk'45'stable_158 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v8) (coe addInt (coe (4 :: Integer)) (coe v5))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v7))
                               (coe v6)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (d_visit'45'walk'45'stable_158
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                                     (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_220 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_rebuild'45'walk'45'stable_220 v0 v1 v4 v5 v6
du_rebuild'45'walk'45'stable_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_220 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_K_114 v5
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                (coe v1) (coe v2) (coe v3) (coe v4))
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                (coe v1) (coe v2) (coe v3) (coe v4))
      MAlonzo.Code.Once.Type.C__'8853'__118 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                         (coe v1) (coe v6) (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v5)))
                            (coe v4)))
                      (coe
                         du_rebuild'45'walk'45'stable_220 (coe v0) (coe v1) (coe v6)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160 (coe v5)))
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                    (coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                                                                   (coe v1) (coe v5)
                                                                   (coe
                                                                      addInt (coe (4 :: Integer))
                                                                      (coe v3))
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v4)))
                                                                (coe
                                                                   du_rebuild'45'walk'45'stable_220
                                                                   (coe v0) (coe v1) (coe v5)
                                                                   (coe
                                                                      addInt (coe (4 :: Integer))
                                                                      (coe v3))
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v4)))
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                         (coe
                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                            (coe
                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
      MAlonzo.Code.Once.Type.C__'8855'__120 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                            (coe v1) (coe v5) (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe v4))
                         (coe
                            du_rebuild'45'walk'45'stable_220 (coe v0) (coe v1) (coe v5)
                            (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_240
                                           (coe v1) (coe v6)
                                           (coe addInt (coe (4 :: Integer)) (coe v3))
                                           (coe
                                              addInt
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160
                                                 (coe v5))
                                              (coe v4)))
                                        (coe
                                           du_rebuild'45'walk'45'stable_220 (coe v0) (coe v1)
                                           (coe v6) (coe addInt (coe (4 :: Integer)) (coe v3))
                                           (coe
                                              addInt
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_lsize_160
                                                 (coe v5))
                                              (coe v4)))
                                        (coe
                                           du_all'45'stable'63''45'sound_60 (coe v0)
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
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v3)))
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
                                                                            addInt
                                                                            (coe (3 :: Integer))
                                                                            (coe v3)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_276 ~v0 ~v1 ~v2 v3 v4
  = du_cata'45'trace'45'nat'45'stable_276 v3 v4
du_cata'45'trace'45'nat'45'stable_276 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_276 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                                          (coe v0)
                                                                                          (coe v1)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                                                                                       (coe
                                                                                                                                          v0)
                                                                                                                                       (coe
                                                                                                                                          v1)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))))))))))))))))))))))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_292 v0 ~v1 v2 v3 v4
  = du_cata'45'trace'45'linear'45'stable_292 v0 v2 v3 v4
du_cata'45'trace'45'linear'45'stable_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                                    (coe v2)
                                                                                    (coe v3)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                                                                                                                  (coe
                                                                                                                                                                     v2)
                                                                                                                                                                  (coe
                                                                                                                                                                     v3)
                                                                                                                                                                  (coe
                                                                                                                                                                     du_all'45'stable'63''45'sound_60
                                                                                                                                                                     (coe
                                                                                                                                                                        v0)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8323'_108
                                                                                                                                                                        (coe
                                                                                                                                                                           v1)))))))))))))))))))))))))))))))))))))))))))))))))))))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.branching-true
d_branching'45'true_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branching'45'true_310 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.I₁-true
d_I'8321''45'true_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'true_326 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_336 v0 v1 v2 v3 v4 ~v5
  = du_cata'45'trace'45'branching'45'stable_336 v0 v1 v2 v3 v4
du_cata'45'trace'45'branching'45'stable_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_336 v0 v1 v2 v3 v4
  = coe
      du_all'45'stable'63''45'sound_60 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'branching_304
               (coe v1) (coe v2) (coe v3) (coe v4))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_18 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_356 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_20
        -> coe v5
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_22
        -> coe du_cata'45'trace'45'nat'45'stable_276 (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_24
        -> coe
             du_cata'45'trace'45'linear'45'stable_292 (coe v0) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_26 v6
        -> coe
             du_cata'45'trace'45'branching'45'stable_336 (coe v0) (coe v6)
             (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-stable
d_ir'45'stable_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_402 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v1) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
             (coe
                d_ir'45'stable_402 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                (coe v5))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (d_ir'45'stable_402
                   (coe v0) (coe v7) (coe v2) (coe v9)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                         (coe v1) (coe v7) (coe v4) (coe v5) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                            (coe v1) (coe v7) (coe v4) (coe v5) (coe v10))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                 (coe
                                    du_trc_24
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v1) (coe v12) (coe addInt (coe (3 :: Integer)) (coe v4))
                                       (coe v5) (coe v9)))
                                 (coe
                                    d_ir'45'stable_402 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (3 :: Integer)) (coe v4)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                          (coe
                                             du_trc_24
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v1) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                      (coe v1) (coe v12)
                                                      (coe addInt (coe (3 :: Integer)) (coe v4))
                                                      (coe v5) (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                         (coe v1) (coe v12)
                                                         (coe addInt (coe (3 :: Integer)) (coe v4))
                                                         (coe v5) (coe v9))))
                                                (coe v10)))
                                          (coe
                                             d_ir'45'stable_402 (coe v0) (coe v1) (coe v13)
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                   (coe v1) (coe v12)
                                                   (coe addInt (coe (3 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                      (coe v1) (coe v12)
                                                      (coe addInt (coe (3 :: Integer)) (coe v4))
                                                      (coe v5) (coe v9)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                 (coe
                                    du_trc_24
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                       (coe v1) (coe v12) (coe addInt (coe (4 :: Integer)) (coe v4))
                                       (coe v5) (coe v9)))
                                 (coe
                                    d_ir'45'stable_402 (coe v0) (coe v1) (coe v12) (coe v9)
                                    (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                          (coe
                                             du_trc_24
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                (coe v1) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                      (coe v1) (coe v12)
                                                      (coe addInt (coe (4 :: Integer)) (coe v4))
                                                      (coe v5) (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                         (coe v1) (coe v12)
                                                         (coe addInt (coe (4 :: Integer)) (coe v4))
                                                         (coe v5) (coe v9))))
                                                (coe v10)))
                                          (coe
                                             d_ir'45'stable_402 (coe v0) (coe v1) (coe v13)
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                   (coe v1) (coe v12)
                                                   (coe addInt (coe (4 :: Integer)) (coe v4))
                                                   (coe v5) (coe v9)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                      (coe v1) (coe v12)
                                                      (coe addInt (coe (4 :: Integer)) (coe v4))
                                                      (coe v5) (coe v9)))))
                                          (coe
                                             du_all'45'stable'63''45'sound_60 (coe v0)
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
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v4)))
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
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v4)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v9)) (coe v2)
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_fst_44)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8) (coe v2)) (coe v2)
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_snd_50)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> coe
                    seq (coe v8)
                    (coe
                       du_all'45'stable'63''45'sound_60 (coe v0)
                       (coe
                          du_trc_24
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe v1)
                             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v10))
                             (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inl_56 v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> coe
                    seq (coe v8)
                    (coe
                       du_all'45'stable'63''45'sound_60 (coe v0)
                       (coe
                          du_trc_24
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe v1) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v1))
                             (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_inr_62 v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                             (coe
                                du_trc_24
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                   (coe v12) (coe v2)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                         (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                            (coe v11) (coe v2) (coe v4)
                                            (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9))))
                                   (coe v10)))
                             (coe
                                d_ir'45'stable_402 (coe v0) (coe v12) (coe v2) (coe v10)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                      (coe v11) (coe v2) (coe v4)
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                         (coe v11) (coe v2) (coe v4)
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v9)))))
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                            (coe
                                               du_trc_24
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                  (coe v11) (coe v2) (coe v4)
                                                  (coe addInt (coe (2 :: Integer)) (coe v5))
                                                  (coe v9)))
                                            (coe
                                               d_ir'45'stable_402 (coe v0) (coe v11) (coe v2)
                                               (coe v9) (coe v4)
                                               (coe addInt (coe (2 :: Integer)) (coe v5)))
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_terminal_74)))
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_initial_78)))
      MAlonzo.Code.Once.IR.C_curry_86 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                (coe
                                                   du_trc_24
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                                                         (coe v11))
                                                      (coe v12) (coe (0 :: Integer))
                                                      (coe addInt (coe (2 :: Integer)) (coe v5))
                                                      (coe v9)))
                                                (coe
                                                   d_ir'45'stable_402 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                                                      (coe v11))
                                                   (coe v12) (coe v9) (coe (0 :: Integer))
                                                   (coe addInt (coe (2 :: Integer)) (coe v5)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                               (coe
                                                                  du_trc_24
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                        (coe v1) (coe v11))
                                                                     (coe v12) (coe (0 :: Integer))
                                                                     (coe
                                                                        addInt (coe (2 :: Integer))
                                                                        (coe v5))
                                                                     (coe v9)))
                                                               (coe
                                                                  d_ir'45'stable_402 (coe v0)
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                     (coe v1) (coe v11))
                                                                  (coe v12) (coe v9)
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v5)))
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                      -> coe
                           du_all'45'stable'63''45'sound_60 (coe v0)
                           (coe
                              du_trc_24
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v10) (coe v2))
                                    (coe v10))
                                 (coe v2) (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v7 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    d_cata'45'dispatch'45'slot'45'stable_356 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'strategy_48
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                             (coe v2) (coe v4) (coe v5) (coe v9))))
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                          (coe v2) (coe v4) (coe v5) (coe v9)))
                    (coe
                       d_ir'45'stable_402 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v2))
                       (coe v2) (coe v9) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v7 v9
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Para_112 v7 v9)))
      MAlonzo.Code.Once.IR.C_Out_116 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v1))
                          (coe v4) (coe v5) (coe MAlonzo.Code.Once.IR.C_Out_116 v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v2) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_120 v7 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_126 v7 v9
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Ana_126 v7 v9)))
      MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_134 v6 v8 v9 v11 v12)))
      MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe v1) (coe v2) (coe v4) (coe v5)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_142 v6 v8 v9 v11 v12)))
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v6
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v4) (coe v5) (coe v3)))
      MAlonzo.Code.Once.IR.C_const_148 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    du_all'45'stable'63''45'sound_60 (coe v0)
                    (coe
                       du_trc_24
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.IR.C_const_148 v7 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
        -> coe
             du_all'45'stable'63''45'sound_60 (coe v0)
             (coe
                du_trc_24
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_346
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7)) (coe v4)
                   (coe v5) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_550 v0 v1 v2 v3
  = coe
      d_ir'45'stable_402 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe (0 :: Integer)) (coe (0 :: Integer))
