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

module MAlonzo.Code.Once.CCC.Codegen.RoomChecks where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.StackDepth
import qualified MAlonzo.Code.Once.CCC.Codegen.StackDepthTable
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.RoomChecks.entry-frame
d_entry'45'frame_8 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  Integer
d_entry'45'frame_8 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v3 v4
                  -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks.max-entry
d_max'45'entry_12 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer
d_max'45'entry_12 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe d_entry'45'frame_8 (coe v1)) (coe d_max'45'entry_12 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks._⊕ʳ_
d__'8853''691'__18 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d__'8853''691'__18 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v1)))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v1)))
-- Once.CCC.Codegen.RoomChecks.r0
d_r0_24 :: MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_r0_24
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Codegen.RoomChecks.tot
d_tot_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 -> Integer
d_tot_26 v0
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v0))
-- Once.CCC.Codegen.RoomChecks.cells
d_cells_30 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  Integer
d_cells_30 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2490 v2
           -> coe v2
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks.stack-k
d_stack'45'k_34 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> Integer
d_stack'45'k_34 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_chk_298 (coe v0)
                (coe v1) (coe v3))
             (coe
                addInt (coe (1 :: Integer))
                (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_dep_274 v0 v3))
             (coe (0 :: Integer))
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_clo'45'chk_280 v0 v1)
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_clo'45'dep_282
                   (coe v0)))
             (coe (0 :: Integer))
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'sig_66 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_sig'45'chk_284 (coe v0))
             (coe v3) (coe (0 :: Integer))
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v3 v4
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'label_70 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'jump_72 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'branch_74 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'ret_76
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'start_78
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'none_80
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.spend
d_spend_80 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_spend_80 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
      (coe d_cells_30 (coe v2))
      (coe
         d_stack'45'k_34 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v2)))
-- Once.CCC.Codegen.RoomChecks.boundary-k
d_boundary'45'k_88 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> Bool
d_boundary'45'k_88 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'sig_66 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'label_70 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'jump_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'branch_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'ret_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'start_78
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'none_80
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.boundary?
d_boundary'63'_90 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 -> Bool
d_boundary'63'_90 v0
  = coe
      d_boundary'45'k_88
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v0))
-- Once.CCC.Codegen.RoomChecks.stretch
d_stretch_94 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_stretch_94 v0 v1 v2
  = case coe v2 of
      [] -> coe d_r0_24
      (:) v3 v4
        -> coe
             d__'8853''691'__18
             (coe
                d_spend_80 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                   (coe v3))
                (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_boundary'63'_90 (coe v3)) (coe d_r0_24)
                (coe
                   d_stretch_94 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                      (coe v3))
                   (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.checks
d_checks_108 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_checks_108 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_boundary'63'_90 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498
                      (coe
                         d_stretch_94 (coe v0)
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                            (coe v3))
                         (coe v4)))
                   (coe
                      d_checks_108 (coe v0)
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                         (coe v3))
                      (coe v4)))
                (coe
                   d_checks_108 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                      (coe v3))
                   (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.pick-by
d_pick'45'by_122 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  Bool -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_pick'45'by_122 v0 v1 v2
  = if coe v2
      then coe v1
      else coe
             MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_T'8320'_986
             (coe d_max'45'entry_12 (coe v0))
-- Once.CCC.Codegen.RoomChecks.pick-of
d_pick'45'of_132 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_pick'45'of_132 v0 v1
  = coe
      d_pick'45'by_122 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_consistent'63'_460
         (coe v1)
         (coe
            d_checks_108 (coe v1)
            (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
            (coe v0)))
-- Once.CCC.Codegen.RoomChecks.pick
d_pick_138 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_pick_138 v0
  = coe
      d_pick'45'of_132 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.StackDepthTable.d_table_846 (coe v0))
-- Once.CCC.Codegen.RoomChecks.room-checks
d_room'45'checks_142 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_room'45'checks_142 v0
  = coe
      d_checks_108 (coe d_pick_138 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
      (coe v0)
-- Once.CCC.Codegen.RoomChecks.room-checks-def
d_room'45'checks'45'def_148 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_room'45'checks'45'def_148 = erased
-- Once.CCC.Codegen.RoomChecks.room-rest
d_room'45'rest_152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_room'45'rest_152 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_drop_542 (coe (1 :: Integer))
      (coe
         d_room'45'checks_142
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1)))
-- Once.CCC.Codegen.RoomChecks.room-checks-∷
d_room'45'checks'45''8759'_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_room'45'checks'45''8759'_166 = erased
-- Once.CCC.Codegen.RoomChecks.room?
d_room'63'_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 -> Bool
d_room'63'_172 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks.till-check
d_till'45'check_174 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_till'45'check_174 v0 v1 v2
  = case coe v2 of
      [] -> coe d_r0_24
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_room'63'_172 (coe v3)) (coe d_r0_24)
             (coe
                d__'8853''691'__18
                (coe
                   d_spend_80 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                      (coe v3))
                   (coe v3))
                (coe
                   d_till'45'check_174 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
                      (coe v3))
                   (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.strip
d_strip_188 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_strip_188 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_room'63'_172 (coe v1)) (coe d_strip_188 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                (coe d_strip_188 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.tbl
d_tbl_194 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_tbl_194 v0 = coe d_pick_138 (coe d_strip_188 (coe v0))
-- Once.CCC.Codegen.RoomChecks.need
d_need_198 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_need_198 v0 v1
  = coe
      d_till'45'check_174 (coe d_tbl_194 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_before'45'from_142
         (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
         (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.List.Base.du_drop_542 (coe v1) (coe v0))
