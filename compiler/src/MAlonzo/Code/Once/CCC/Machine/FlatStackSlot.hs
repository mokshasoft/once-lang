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

module MAlonzo.Code.Once.CCC.Machine.FlatStackSlot where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.FlatStackSlot._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_94
du_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_94
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2462
-- Once.CCC.Machine.FlatStackSlot._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_104 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_104
du_exec'45'restore'45'input'45'with'45'value_104 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2474
-- Once.CCC.Machine.FlatStackSlot._.FlatState
d_FlatState_164 a0 = ()
-- Once.CCC.Machine.FlatStackSlot._.do-branch
d_do'45'branch_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_232 (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.do-jump
d_do'45'jump_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_174 ~v0 = du_do'45'jump_174
du_do'45'jump_174 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_174
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_224
-- Once.CCC.Machine.FlatStackSlot._.flat-exec-instr
d_flat'45'exec'45'instr_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_232 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.FlatState.falloc
d_falloc_296 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_296 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.FlatState.fclosure
d_fclosure_298 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_298 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.FlatState.floc
d_floc_300 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_300 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.FlatState.fpc
d_fpc_302 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_302 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Machine.FlatStackSlot._.FlatState.fret
d_fret_304 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_304 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Machine.FlatStackSlot.SameFrames
d_SameFrames_310 a0 a1 a2 = ()
data T_SameFrames_310 = C_mkSameFrames_328
-- Once.CCC.Machine.FlatStackSlot.SameFrames.sf-slots
d_sf'45'slots_322 ::
  T_SameFrames_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sf'45'slots_322 = erased
-- Once.CCC.Machine.FlatStackSlot.SameFrames.sf-saved
d_sf'45'saved_324 ::
  T_SameFrames_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sf'45'saved_324 = erased
-- Once.CCC.Machine.FlatStackSlot.SameFrames.sf-ret
d_sf'45'ret_326 ::
  T_SameFrames_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sf'45'ret_326 = erased
-- Once.CCC.Machine.FlatStackSlot.sf-refl
d_sf'45'refl_332 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SameFrames_310
d_sf'45'refl_332 = erased
-- Once.CCC.Machine.FlatStackSlot.sf-jump
d_sf'45'jump_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SameFrames_310
d_sf'45'jump_340 = erased
-- Once.CCC.Machine.FlatStackSlot.sf-branch
d_sf'45'branch_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SameFrames_310
d_sf'45'branch_356 = erased
-- Once.CCC.Machine.FlatStackSlot.ss-mv
d_ss'45'mv_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ss'45'mv_376 = erased
-- Once.CCC.Machine.FlatStackSlot.ss-mv-saved
d_ss'45'mv'45'saved_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ss'45'mv'45'saved_394 = erased
-- Once.CCC.Machine.FlatStackSlot.ss-mv-ri
d_ss'45'mv'45'ri_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ss'45'mv'45'ri_412 = erased
-- Once.CCC.Machine.FlatStackSlot.ss-mv-ri-saved
d_ss'45'mv'45'ri'45'saved_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ss'45'mv'45'ri'45'saved_430 = erased
-- Once.CCC.Machine.FlatStackSlot.flat-same-frames
d_flat'45'same'45'frames_448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny -> T_SameFrames_310
d_flat'45'same'45'frames_448 = erased
