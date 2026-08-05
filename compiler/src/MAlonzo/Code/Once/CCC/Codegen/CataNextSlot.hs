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

module MAlonzo.Code.Once.CCC.Codegen.CataNextSlot where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState
d_FlatState_14 a0 = ()
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-flat
d_exec'45'flat_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_exec'45'flat_42 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_618 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.flat-exec-instr
d_flat'45'exec'45'instr_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState.falloc
d_falloc_146 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_146 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState.fclosure
d_fclosure_148 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_148 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState.floc
d_floc_150 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_150 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState.fpc
d_fpc_152 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_152 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.FlatState.fret
d_fret_154 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_154 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-abstract
d_exec'45'abstract_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_164 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
      (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-case-dispatch
d_exec'45'case'45'dispatch_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2772
      (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_168 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_168
du_exec'45'load'45'from'45'slot'45'with'45'value_168 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_168
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2462
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_170 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_170
du_exec'45'restore'45'input'45'with'45'value_170 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_170
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2474
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot._.exec-trace
d_exec'45'trace_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.elfs-alloc
d_elfs'45'alloc_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elfs'45'alloc_180 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.eris-alloc
d_eris'45'alloc_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eris'45'alloc_198 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.SlotStable
d_SlotStable_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_SlotStable_210 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.SlotStableT
d_SlotStableT_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_SlotStableT_212 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.abstract-keeps-next-slot
d_abstract'45'keeps'45'next'45'slot_228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abstract'45'keeps'45'next'45'slot_228 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.trace-keeps-next-slot
d_trace'45'keeps'45'next'45'slot_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'keeps'45'next'45'slot_236 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.case-keeps-next-slot
d_case'45'keeps'45'next'45'slot_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'keeps'45'next'45'slot_248 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.flat-keeps-next-slot
d_flat'45'keeps'45'next'45'slot_544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'keeps'45'next'45'slot_544 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.AllSlotStable
d_AllSlotStable_900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_AllSlotStable_900 = erased
-- Once.CCC.Codegen.CataNextSlot.CataNextSlot.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_908 = erased
