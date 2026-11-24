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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Type

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
-- Once.CCC.Codegen.RoomChecks.block-scratch
d_block'45'scratch_22 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
d_block'45'scratch_22 ~v0 v1 v2 = du_block'45'scratch_22 v1 v2
du_block'45'scratch_22 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
du_block'45'scratch_22 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_322 (coe v1))
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.sigop-call-words
d_sigop'45'call'45'words_28 :: Integer
d_sigop'45'call'45'words_28 = coe (5 :: Integer)
-- Once.CCC.Codegen.RoomChecks.sigop-scratch
d_sigop'45'scratch_34 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Integer
d_sigop'45'scratch_34 ~v0 ~v1 v2 = du_sigop'45'scratch_34 v2
du_sigop'45'scratch_34 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Integer
du_sigop'45'scratch_34 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v2 v3 v4
           -> coe du_block'45'scratch_22 (coe v3) (coe v4)
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks._⊕ʳ_
d__'8853''691'__38 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d__'8853''691'__38 v0 v1
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
d_r0_44 :: MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_r0_44
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Codegen.RoomChecks.tot
d_tot_46 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418 -> Integer
d_tot_46 v0
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v0))
-- Once.CCC.Codegen.RoomChecks.spend
d_spend_50 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_spend_50 v0 v1
  = let v2 = d_r0_44 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2462
           -> coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2476 v3 v4 v5
           -> coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
                (coe (0 :: Integer))
                (coe
                   addInt
                   (coe
                      du_sigop'45'scratch_34
                      (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v5)))
                   (coe d_sigop'45'call'45'words_28))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2490 v3
           -> coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428 (coe v3)
                (coe (0 :: Integer))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v4 v5
                  -> coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
                       (coe (0 :: Integer)) (coe v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v4
                  -> coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_room_2428
                       (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v0))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.RoomChecks.boundary?
d_boundary'63'_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 -> Bool
d_boundary'63'_70 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2462
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks.stretch
d_stretch_72 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_stretch_72 v0 v1
  = case coe v1 of
      [] -> coe d_r0_44
      (:) v2 v3
        -> coe
             d__'8853''691'__38 (coe d_spend_50 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_boundary'63'_70 (coe v2)) (coe d_r0_44)
                (coe d_stretch_72 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.checks
d_checks_82 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_checks_82 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_boundary'63'_70 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498
                      (coe d_stretch_72 (coe v0) (coe v3)))
                   (coe d_checks_82 (coe v0) (coe v3)))
                (coe d_checks_82 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.room-checks
d_room'45'checks_92 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_room'45'checks_92 v0
  = coe d_checks_82 (coe d_max'45'entry_12 (coe v0)) (coe v0)
-- Once.CCC.Codegen.RoomChecks.room?
d_room'63'_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 -> Bool
d_room'63'_96 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.RoomChecks.till-check
d_till'45'check_98 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_till'45'check_98 v0 v1
  = case coe v1 of
      [] -> coe d_r0_44
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_room'63'_96 (coe v2)) (coe d_r0_44)
             (coe
                d__'8853''691'__38 (coe d_spend_50 (coe v0) (coe v2))
                (coe d_till'45'check_98 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.RoomChecks.need
d_need_108 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Room_2418
d_need_108 v0 v1
  = coe
      d_till'45'check_98 (coe d_max'45'entry_12 (coe v0))
      (coe MAlonzo.Code.Data.List.Base.du_drop_542 (coe v1) (coe v0))
