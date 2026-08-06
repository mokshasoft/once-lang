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

module MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.FlatRegTagWF._.writeLoc
d_writeLoc_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_32 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_878 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'lea'45'indexed'45'via_60 ~v0
  = du_exec'45'lea'45'indexed'45'via_60
du_exec'45'lea'45'indexed'45'via_60 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'lea'45'indexed'45'via_60
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1558
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_66 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_66
du_exec'45'load'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_66
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_68 ~v0
  = du_exec'45'load'45'via'45'resolved_68
du_exec'45'load'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_68
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1532
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'with'45'value_70 ~v0
  = du_exec'45'load'45'with'45'value_70
du_exec'45'load'45'with'45'value_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'with'45'value_70
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1520
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1582
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1544
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.BodyRunner
d_BodyRunner_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_84 = erased
-- Once.CCC.Machine.FlatRegTagWF._.exec-abstract
d_exec'45'abstract_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_90 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_94 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2876
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_100 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_100
du_exec'45'load'45'from'45'slot'45'with'45'value_100 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_100
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2566
-- Once.CCC.Machine.FlatRegTagWF._.exec-loop-run
d_exec'45'loop'45'run_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_104 ~v0 = du_exec'45'loop'45'run_104
du_exec'45'loop'45'run_104 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2814
-- Once.CCC.Machine.FlatRegTagWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_110 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_110
du_exec'45'restore'45'input'45'with'45'value_110 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_110
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2578
-- Once.CCC.Machine.FlatRegTagWF._.exec-trace
d_exec'45'trace_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2872 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_loop'45'reanchor'45'alloc_146 ~v0
  = du_loop'45'reanchor'45'alloc_146
du_loop'45'reanchor'45'alloc_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_loop'45'reanchor'45'alloc_146
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2808
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_loop'45'reanchor'45'loc_148 ~v0 = du_loop'45'reanchor'45'loc_148
du_loop'45'reanchor'45'loc_148 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_loop'45'reanchor'45'loc_148
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2802
-- Once.CCC.Machine.FlatRegTagWF._.CallPost
d_CallPost_170 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatRegTagWF._.FlatState
d_FlatState_172 a0 = ()
-- Once.CCC.Machine.FlatRegTagWF._.do-branch
d_do'45'branch_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_186 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_512 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.do-call
d_do'45'call_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_188 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_914 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.do-jump
d_do'45'jump_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_196 ~v0 = du_do'45'jump_196
du_do'45'jump_196 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_196
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_504
-- Once.CCC.Machine.FlatRegTagWF._.do-ret
d_do'45'ret_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_198 ~v0 = du_do'45'ret_198
du_do'45'ret_198 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_198
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_714
-- Once.CCC.Machine.FlatRegTagWF._.flat-exec-instr
d_flat'45'exec'45'instr_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_266 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.falloc
d_falloc_348 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_348 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fclosure
d_fclosure_350 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_350 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.floc
d_floc_352 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_352 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fpc
d_fpc_354 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_354 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fret
d_fret_356 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_356 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.IsTag
d_IsTag_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTag_358 = erased
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF
d_RegTagWF_366 a0 a1 = ()
data T_RegTagWF_366
  = C_mkRegTagWF_378 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.scratch-tag
d_scratch'45'tag_374 ::
  T_RegTagWF_366 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'tag_374 v0
  = case coe v0 of
      C_mkRegTagWF_378 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.count-tag
d_count'45'tag_376 ::
  T_RegTagWF_366 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'tag_376 v0
  = case coe v0 of
      C_mkRegTagWF_378 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.IsTagP
d_IsTagP_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTagP_380 = erased
-- Once.CCC.Machine.FlatRegTagWF.is-tag-P
d_is'45'tag'45'P_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_is'45'tag'45'P_384 ~v0 ~v1 v2 = du_is'45'tag'45'P_384 v2
du_is'45'tag'45'P_384 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_is'45'tag'45'P_384 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatRegTagWF.sv-succ-tag
d_sv'45'succ'45'tag_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'succ'45'tag_390 ~v0 ~v1 v2 = du_sv'45'succ'45'tag_390 v2
du_sv'45'succ'45'tag_390 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'succ'45'tag_390 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (1 :: Integer)) (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.sv-pred-tag
d_sv'45'pred'45'tag_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'pred'45'tag_396 ~v0 ~v1 v2 = du_sv'45'pred'45'tag_396 v2
du_sv'45'pred'45'tag_396 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'pred'45'tag_396 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    erased
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-other
d_regtag'45'write'45'other_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'other_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'other_406 v6
du_regtag'45'write'45'other_406 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'other_406 v0
  = coe
      C_mkRegTagWF_378
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_374 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_376 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in1
d_regtag'45'write'45'in1_424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'in1_424 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in1_424 v3
du_regtag'45'write'45'in1_424 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'in1_424 v0
  = coe du_regtag'45'write'45'other_406 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in2
d_regtag'45'write'45'in2_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'in2_436 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in2_436 v3
du_regtag'45'write'45'in2_436 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'in2_436 v0
  = coe du_regtag'45'write'45'other_406 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-out
d_regtag'45'write'45'out_448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'out_448 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'out_448 v3
du_regtag'45'write'45'out_448 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'out_448 v0
  = coe du_regtag'45'write'45'other_406 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-transport
d_regtag'45'transport_460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'transport_460 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_regtag'45'transport_460 v5
du_regtag'45'transport_460 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'transport_460 v0
  = coe
      C_mkRegTagWF_378
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_374 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_376 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-halt
d_regtag'45'halt_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'halt_472 ~v0 ~v1 v2 = du_regtag'45'halt_472 v2
du_regtag'45'halt_472 :: T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'halt_472 v0 = coe du_regtag'45'transport_460 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.NonCounter
d_NonCounter_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> ()
d_NonCounter_478 = erased
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc
d_regtag'45'write'45'nc_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'nc_486 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_regtag'45'write'45'nc_486 v2 v5
du_regtag'45'write'45'nc_486 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'nc_486 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_460 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc-halt
d_regtag'45'write'45'nc'45'halt_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'nc'45'halt_514 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'nc'45'halt_514 v2 v6
du_regtag'45'write'45'nc'45'halt_514 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'nc'45'halt_514 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_460 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-scratch
d_regtag'45'set'45'scratch_544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'set'45'scratch_544 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'scratch_544 v3 v4
du_regtag'45'set'45'scratch_544 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'set'45'scratch_544 v0 v1
  = coe C_mkRegTagWF_378 (coe v0) (coe d_count'45'tag_376 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-count
d_regtag'45'set'45'count_558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'set'45'count_558 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'count_558 v3 v4
du_regtag'45'set'45'count_558 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'set'45'count_558 v0 v1
  = coe C_mkRegTagWF_378 (coe d_scratch'45'tag_374 (coe v1)) (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-loc
d_regtag'45'write'45'loc_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'write'45'loc_574 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'write'45'loc_574 v2 v3 v4
du_regtag'45'write'45'loc_574 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'write'45'loc_574 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe du_regtag'45'transport_460 (coe v2)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
               -> coe seq (coe v4) (coe du_regtag'45'transport_460 (coe v2))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
               -> coe du_regtag'45'transport_460 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
               -> coe du_regtag'45'transport_460 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
               -> coe du_regtag'45'transport_460 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-value
d_regtag'45'load'45'value_636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'load'45'value_636 ~v0 ~v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'value_636 v2 v4 v5
du_regtag'45'load'45'value_636 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'load'45'value_636 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'nc_486 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-resolved
d_regtag'45'load'45'resolved_658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'load'45'resolved_658 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'resolved_658 v1 v2 v4 v5
du_regtag'45'load'45'resolved_658 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'load'45'resolved_658 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_636 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-suc-resolved
d_regtag'45'load'45'suc'45'resolved_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'load'45'suc'45'resolved_682 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'suc'45'resolved_682 v1 v2 v4 v5
du_regtag'45'load'45'suc'45'resolved_682 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'load'45'suc'45'resolved_682 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_636 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-resolved
d_regtag'45'store'45'resolved_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'store'45'resolved_706 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'resolved_706 v2 v3 v4
du_regtag'45'store'45'resolved_706 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'store'45'resolved_706 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'loc_574 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-suc-resolved
d_regtag'45'store'45'suc'45'resolved_724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'store'45'suc'45'resolved_724 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'suc'45'resolved_724 v2 v3 v4
du_regtag'45'store'45'suc'45'resolved_724 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'store'45'suc'45'resolved_724 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_regtag'45'write'45'loc_574
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v3))
             (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-lea-indexed
d_regtag'45'lea'45'indexed_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'lea'45'indexed_742 ~v0 ~v1 v2 ~v3 v4
  = du_regtag'45'lea'45'indexed_742 v2 v4
du_regtag'45'lea'45'indexed_742 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'lea'45'indexed_742 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-out
d_regtag'45'slot'45'load'45'out_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'slot'45'load'45'out_760 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'out_760 v1 v4
du_regtag'45'slot'45'load'45'out_760 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'slot'45'load'45'out_760 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-in1
d_regtag'45'slot'45'load'45'in1_782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'slot'45'load'45'in1_782 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'in1_782 v1 v4
du_regtag'45'slot'45'load'45'in1_782 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'slot'45'load'45'in1_782 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run
d_regtag'45'loop'45'run_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   T_RegTagWF_366 -> T_RegTagWF_366) ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'loop'45'run_810 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe du_regtag'45'halt_472 (coe v6)
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v8
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v3) in
              coe
                (if coe v8
                   then coe v6
                   else (let v9
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_146
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v3)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_824 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v10
                                -> case coe v10 of
                                     0 -> coe v6
                                     _ -> coe
                                            d_regtag'45'loop'45'run'45'go_824 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v10 v11 v12
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_824 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_824 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run-go
d_regtag'45'loop'45'run'45'go_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   T_RegTagWF_366 -> T_RegTagWF_366) ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'loop'45'run'45'go_824 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_regtag'45'loop'45'run_810 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2802
         (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v3 v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2808
         (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1 v3 v4)))
      (coe v5) (coe du_regtag'45'transport_460 (coe v5 v3 v4 v6))
-- Once.CCC.Machine.FlatRegTagWF.regtag-abstract
d_regtag'45'abstract_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'abstract_960 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             du_regtag'45'load'45'resolved_658 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             du_regtag'45'load'45'suc'45'resolved_682 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_760
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v5
        -> coe
             du_regtag'45'write'45'loc_574
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             du_regtag'45'store'45'resolved_706
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             du_regtag'45'store'45'suc'45'resolved_724
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v5
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v5
        -> coe
             du_regtag'45'slot'45'load'45'in1_782
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v5
        -> coe
             du_regtag'45'write'45'loc_574
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_760
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc'45'halt_514
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v5
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v5
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v5 v6
        -> coe
             d_regtag'45'case_980 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2786
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v5
        -> coe
             du_regtag'45'write'45'nc_486
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v5
        -> coe
             d_regtag'45'loop'45'run_810 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2872 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_regtag'45'trace_968 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
               -> coe
                    du_regtag'45'set'45'scratch_544
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
               -> coe
                    du_regtag'45'set'45'scratch_544
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
               -> coe
                    du_regtag'45'set'45'scratch_544
                    (coe du_sv'45'pred'45'tag_396 (coe d_scratch'45'tag_374 (coe v4)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
               -> coe
                    du_regtag'45'set'45'scratch_544 (coe d_count'45'tag_376 (coe v4))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
               -> coe
                    du_regtag'45'set'45'count_558
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
               -> coe
                    du_regtag'45'set'45'count_558
                    (coe du_sv'45'succ'45'tag_390 (coe d_count'45'tag_376 (coe v4)))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v5
        -> coe
             du_regtag'45'lea'45'indexed_742
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1554
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                         (coe v3))
                      (coe v5))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-trace
d_regtag'45'trace_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'trace_968 v0 v1 v2 v3 v4
  = case coe v1 of
      [] -> coe v4
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v2) in
           coe
             (if coe v7
                then coe v4
                else coe
                       d_regtag'45'trace_968 (coe v0) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          d_regtag'45'abstract_960 (coe v0) (coe v5) (coe v2) (coe v3)
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-case
d_regtag'45'case_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'case_980 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v8
               -> coe du_regtag'45'halt_472 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v8
               -> case coe v8 of
                    0 -> coe
                           d_regtag'45'trace_968 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_regtag'45'trace_968 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v8 v9 v10
               -> coe du_regtag'45'halt_472 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v8
               -> coe du_regtag'45'halt_472 (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.FlatRegTag
d_FlatRegTag_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_1360 = erased
-- Once.CCC.Machine.FlatRegTagWF.flat-scratch-is-tag
d_flat'45'scratch'45'is'45'tag_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'scratch'45'is'45'tag_1368 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'scratch'45'is'45'tag_1368 v3
du_flat'45'scratch'45'is'45'tag_1368 :: T_RegTagWF_366 -> AgdaAny
du_flat'45'scratch'45'is'45'tag_1368 v0
  = coe
      du_is'45'tag'45'P_384
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_374 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.flat-count-is-tag
d_flat'45'count'45'is'45'tag_1382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'count'45'is'45'tag_1382 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'count'45'is'45'tag_1382 v3
du_flat'45'count'45'is'45'tag_1382 :: T_RegTagWF_366 -> AgdaAny
du_flat'45'count'45'is'45'tag_1382 v0
  = coe
      du_is'45'tag'45'P_384
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_376 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-jump
d_regtag'45'jump_1396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'jump_1396 ~v0 v1 ~v2 v3 = du_regtag'45'jump_1396 v1 v3
du_regtag'45'jump_1396 ::
  Maybe Integer -> T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'jump_1396 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_472 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-branch
d_regtag'45'branch_1416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'branch_1416 v0 v1 v2 v3 ~v4 v5
  = du_regtag'45'branch_1416 v0 v1 v2 v3 v5
du_regtag'45'branch_1416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'branch_1416 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_regtag'45'jump_1396
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatRegTagWF.regtag-ret
d_regtag'45'ret_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'ret_1438 ~v0 v1 ~v2 v3 = du_regtag'45'ret_1438 v1 v3
du_regtag'45'ret_1438 ::
  [Integer] -> T_RegTagWF_366 -> T_RegTagWF_366
du_regtag'45'ret_1438 v0 v1
  = case coe v0 of
      [] -> coe du_regtag'45'halt_472 (coe v1)
      (:) v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-call
d_regtag'45'call_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_regtag'45'call_1456 v0 v1 v2 v3
  = coe
      du_go_1468 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_942 (coe v0) (coe v1)
         (coe v2))
-- Once.CCC.Machine.FlatRegTagWF._.go
d_go_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_924 -> T_RegTagWF_366
d_go_1468 ~v0 ~v1 ~v2 v3 v4 = du_go_1468 v3 v4
du_go_1468 ::
  T_RegTagWF_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_924 -> T_RegTagWF_366
du_go_1468 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'halt_930
        -> coe du_regtag'45'halt_472 (coe v0)
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'enter_936 v2 v3
        -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.flat-regtag-step
d_flat'45'regtag'45'step_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_366 -> T_RegTagWF_366
d_flat'45'regtag'45'step_1494 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe d_regtag'45'call_1456 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v5 v6 v7
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v5 v6 v7
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v5 v6
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v6
               -> coe
                    du_regtag'45'jump_1396
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v6
               -> coe
                    du_regtag'45'branch_1416 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_100
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v6
               -> coe
                    du_regtag'45'branch_1416 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_102
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_114
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v6 v7
               -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v6
               -> coe
                    du_regtag'45'ret_1438
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v5
        -> coe
             d_regtag'45'abstract_960 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
