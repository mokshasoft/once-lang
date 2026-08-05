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
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.FlatRegTagWF._.writeLoc
d_writeLoc_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_26 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'lea'45'indexed'45'via_54 ~v0
  = du_exec'45'lea'45'indexed'45'via_54
du_exec'45'lea'45'indexed'45'via_54 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'lea'45'indexed'45'via_54
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1466
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_60 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_60
du_exec'45'load'45'suc'45'via'45'resolved_60 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_60
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1478
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_62 ~v0
  = du_exec'45'load'45'via'45'resolved_62
du_exec'45'load'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1440
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'with'45'value_64 ~v0
  = du_exec'45'load'45'with'45'value_64
du_exec'45'load'45'with'45'value_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'with'45'value_64
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1428
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1490
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1452
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.BodyRunner
d_BodyRunner_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_78 = erased
-- Once.CCC.Machine.FlatRegTagWF._.exec-abstract
d_exec'45'abstract_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2772
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-from-slot-with-value
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
-- Once.CCC.Machine.FlatRegTagWF._.exec-loop-run
d_exec'45'loop'45'run_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_98 ~v0 = du_exec'45'loop'45'run_98
du_exec'45'loop'45'run_98 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_98
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2710
-- Once.CCC.Machine.FlatRegTagWF._.exec-restore-input-with-value
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
-- Once.CCC.Machine.FlatRegTagWF._.exec-trace
d_exec'45'trace_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_loop'45'reanchor'45'alloc_140 ~v0
  = du_loop'45'reanchor'45'alloc_140
du_loop'45'reanchor'45'alloc_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_loop'45'reanchor'45'alloc_140
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2704
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_loop'45'reanchor'45'loc_142 ~v0 = du_loop'45'reanchor'45'loc_142
du_loop'45'reanchor'45'loc_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_loop'45'reanchor'45'loc_142
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2698
-- Once.CCC.Machine.FlatRegTagWF._.FlatState
d_FlatState_164 a0 = ()
-- Once.CCC.Machine.FlatRegTagWF._.do-branch
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
-- Once.CCC.Machine.FlatRegTagWF._.do-jump
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
-- Once.CCC.Machine.FlatRegTagWF._.do-ret
d_do'45'ret_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'ret_176 ~v0 = du_do'45'ret_176
du_do'45'ret_176 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'ret_176
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_430
-- Once.CCC.Machine.FlatRegTagWF._.flat-exec-instr
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
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.falloc
d_falloc_296 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_296 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fclosure
d_fclosure_298 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_298 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.floc
d_floc_300 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_300 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fpc
d_fpc_302 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_302 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fret
d_fret_304 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_304 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.IsTag
d_IsTag_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTag_306 = erased
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF
d_RegTagWF_314 a0 a1 = ()
data T_RegTagWF_314
  = C_mkRegTagWF_326 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.scratch-tag
d_scratch'45'tag_322 ::
  T_RegTagWF_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'tag_322 v0
  = case coe v0 of
      C_mkRegTagWF_326 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.count-tag
d_count'45'tag_324 ::
  T_RegTagWF_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'tag_324 v0
  = case coe v0 of
      C_mkRegTagWF_326 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.IsTagP
d_IsTagP_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTagP_328 = erased
-- Once.CCC.Machine.FlatRegTagWF.is-tag-P
d_is'45'tag'45'P_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_is'45'tag'45'P_332 ~v0 ~v1 v2 = du_is'45'tag'45'P_332 v2
du_is'45'tag'45'P_332 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_is'45'tag'45'P_332 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatRegTagWF.sv-succ-tag
d_sv'45'succ'45'tag_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'succ'45'tag_338 ~v0 ~v1 v2 = du_sv'45'succ'45'tag_338 v2
du_sv'45'succ'45'tag_338 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'succ'45'tag_338 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (1 :: Integer)) (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.sv-pred-tag
d_sv'45'pred'45'tag_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'pred'45'tag_344 ~v0 ~v1 v2 = du_sv'45'pred'45'tag_344 v2
du_sv'45'pred'45'tag_344 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'pred'45'tag_344 v0
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
d_regtag'45'write'45'other_354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'other_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'other_354 v6
du_regtag'45'write'45'other_354 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'other_354 v0
  = coe
      C_mkRegTagWF_326
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_322 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_324 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in1
d_regtag'45'write'45'in1_372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'in1_372 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in1_372 v3
du_regtag'45'write'45'in1_372 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'in1_372 v0
  = coe du_regtag'45'write'45'other_354 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in2
d_regtag'45'write'45'in2_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'in2_384 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in2_384 v3
du_regtag'45'write'45'in2_384 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'in2_384 v0
  = coe du_regtag'45'write'45'other_354 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-out
d_regtag'45'write'45'out_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'out_396 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'out_396 v3
du_regtag'45'write'45'out_396 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'out_396 v0
  = coe du_regtag'45'write'45'other_354 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-transport
d_regtag'45'transport_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'transport_408 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_regtag'45'transport_408 v5
du_regtag'45'transport_408 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'transport_408 v0
  = coe
      C_mkRegTagWF_326
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_322 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_324 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-halt
d_regtag'45'halt_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'halt_420 ~v0 ~v1 v2 = du_regtag'45'halt_420 v2
du_regtag'45'halt_420 :: T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'halt_420 v0 = coe du_regtag'45'transport_408 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.NonCounter
d_NonCounter_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> ()
d_NonCounter_426 = erased
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc
d_regtag'45'write'45'nc_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'nc_434 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_regtag'45'write'45'nc_434 v2 v5
du_regtag'45'write'45'nc_434 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'nc_434 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_408 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc-halt
d_regtag'45'write'45'nc'45'halt_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'nc'45'halt_462 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'nc'45'halt_462 v2 v6
du_regtag'45'write'45'nc'45'halt_462 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'nc'45'halt_462 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_408 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-scratch
d_regtag'45'set'45'scratch_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'set'45'scratch_492 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'scratch_492 v3 v4
du_regtag'45'set'45'scratch_492 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'set'45'scratch_492 v0 v1
  = coe C_mkRegTagWF_326 (coe v0) (coe d_count'45'tag_324 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-count
d_regtag'45'set'45'count_506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'set'45'count_506 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'count_506 v3 v4
du_regtag'45'set'45'count_506 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'set'45'count_506 v0 v1
  = coe C_mkRegTagWF_326 (coe d_scratch'45'tag_322 (coe v1)) (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-loc
d_regtag'45'write'45'loc_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'write'45'loc_522 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'write'45'loc_522 v2 v3 v4
du_regtag'45'write'45'loc_522 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'write'45'loc_522 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe du_regtag'45'transport_408 (coe v2)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
               -> coe seq (coe v4) (coe du_regtag'45'transport_408 (coe v2))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
               -> coe du_regtag'45'transport_408 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
               -> coe du_regtag'45'transport_408 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
               -> coe du_regtag'45'transport_408 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-value
d_regtag'45'load'45'value_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'load'45'value_584 ~v0 ~v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'value_584 v2 v4 v5
du_regtag'45'load'45'value_584 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'load'45'value_584 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'nc_434 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-resolved
d_regtag'45'load'45'resolved_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'load'45'resolved_606 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'resolved_606 v1 v2 v4 v5
du_regtag'45'load'45'resolved_606 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'load'45'resolved_606 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_584 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-suc-resolved
d_regtag'45'load'45'suc'45'resolved_630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'load'45'suc'45'resolved_630 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'suc'45'resolved_630 v1 v2 v4 v5
du_regtag'45'load'45'suc'45'resolved_630 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'load'45'suc'45'resolved_630 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_584 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-resolved
d_regtag'45'store'45'resolved_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'store'45'resolved_654 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'resolved_654 v2 v3 v4
du_regtag'45'store'45'resolved_654 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'store'45'resolved_654 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'loc_522 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-suc-resolved
d_regtag'45'store'45'suc'45'resolved_672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'store'45'suc'45'resolved_672 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'suc'45'resolved_672 v2 v3 v4
du_regtag'45'store'45'suc'45'resolved_672 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'store'45'suc'45'resolved_672 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_regtag'45'write'45'loc_522
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v3))
             (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-lea-indexed
d_regtag'45'lea'45'indexed_690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'lea'45'indexed_690 ~v0 ~v1 v2 ~v3 v4
  = du_regtag'45'lea'45'indexed_690 v2 v4
du_regtag'45'lea'45'indexed_690 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'lea'45'indexed_690 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-out
d_regtag'45'slot'45'load'45'out_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'slot'45'load'45'out_708 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'out_708 v1 v4
du_regtag'45'slot'45'load'45'out_708 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'slot'45'load'45'out_708 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-in1
d_regtag'45'slot'45'load'45'in1_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'slot'45'load'45'in1_730 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'in1_730 v1 v4
du_regtag'45'slot'45'load'45'in1_730 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'slot'45'load'45'in1_730 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run
d_regtag'45'loop'45'run_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   T_RegTagWF_314 -> T_RegTagWF_314) ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'loop'45'run_758 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe du_regtag'45'halt_420 (coe v6)
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
                                     d_regtag'45'loop'45'run'45'go_772 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v10
                                -> case coe v10 of
                                     0 -> coe v6
                                     _ -> coe
                                            d_regtag'45'loop'45'run'45'go_772 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v10 v11 v12
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_772 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_772 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run-go
d_regtag'45'loop'45'run'45'go_772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   T_RegTagWF_314 -> T_RegTagWF_314) ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'loop'45'run'45'go_772 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_regtag'45'loop'45'run_758 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2698
         (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v3 v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2704
         (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1 v3 v4)))
      (coe v5) (coe du_regtag'45'transport_408 (coe v5 v3 v4 v6))
-- Once.CCC.Machine.FlatRegTagWF.regtag-abstract
d_regtag'45'abstract_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'abstract_908 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_regtag'45'load'45'resolved_606 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_regtag'45'load'45'suc'45'resolved_630 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_708
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v5
        -> coe
             du_regtag'45'write'45'loc_522
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_regtag'45'store'45'resolved_654
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_regtag'45'store'45'suc'45'resolved_672
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v5
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v5
        -> coe
             du_regtag'45'slot'45'load'45'in1_730
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v5
        -> coe
             du_regtag'45'write'45'loc_522
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_708
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc'45'halt_462
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v5
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v5
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v5 v6
        -> coe
             d_regtag'45'case_928 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2682
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v5
        -> coe
             du_regtag'45'write'45'nc_434
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v5
        -> coe
             d_regtag'45'loop'45'run_758 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_regtag'45'trace_916 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
               -> coe
                    du_regtag'45'set'45'scratch_492
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
               -> coe
                    du_regtag'45'set'45'scratch_492
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
               -> coe
                    du_regtag'45'set'45'scratch_492
                    (coe du_sv'45'pred'45'tag_344 (coe d_scratch'45'tag_322 (coe v4)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
               -> coe
                    du_regtag'45'set'45'scratch_492 (coe d_count'45'tag_324 (coe v4))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
               -> coe
                    du_regtag'45'set'45'count_506
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
               -> coe
                    du_regtag'45'set'45'count_506
                    (coe du_sv'45'succ'45'tag_338 (coe d_count'45'tag_324 (coe v4)))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v5
        -> coe
             du_regtag'45'lea'45'indexed_690
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1462
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
d_regtag'45'trace_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'trace_916 v0 v1 v2 v3 v4
  = case coe v1 of
      [] -> coe v4
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v2) in
           coe
             (if coe v7
                then coe v4
                else coe
                       d_regtag'45'trace_916 (coe v0) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          d_regtag'45'abstract_908 (coe v0) (coe v5) (coe v2) (coe v3)
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-case
d_regtag'45'case_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'case_928 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v8
               -> coe du_regtag'45'halt_420 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v8
               -> case coe v8 of
                    0 -> coe
                           d_regtag'45'trace_916 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_regtag'45'trace_916 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v8 v9 v10
               -> coe du_regtag'45'halt_420 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v8
               -> coe du_regtag'45'halt_420 (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.FlatRegTag
d_FlatRegTag_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_1308 = erased
-- Once.CCC.Machine.FlatRegTagWF.flat-scratch-is-tag
d_flat'45'scratch'45'is'45'tag_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'scratch'45'is'45'tag_1316 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'scratch'45'is'45'tag_1316 v3
du_flat'45'scratch'45'is'45'tag_1316 :: T_RegTagWF_314 -> AgdaAny
du_flat'45'scratch'45'is'45'tag_1316 v0
  = coe
      du_is'45'tag'45'P_332
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_322 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.flat-count-is-tag
d_flat'45'count'45'is'45'tag_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_314 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'count'45'is'45'tag_1330 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'count'45'is'45'tag_1330 v3
du_flat'45'count'45'is'45'tag_1330 :: T_RegTagWF_314 -> AgdaAny
du_flat'45'count'45'is'45'tag_1330 v0
  = coe
      du_is'45'tag'45'P_332
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_324 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-jump
d_regtag'45'jump_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'jump_1344 ~v0 v1 ~v2 v3 = du_regtag'45'jump_1344 v1 v3
du_regtag'45'jump_1344 ::
  Maybe Integer -> T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'jump_1344 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_420 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-branch
d_regtag'45'branch_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'branch_1364 v0 v1 v2 v3 ~v4 v5
  = du_regtag'45'branch_1364 v0 v1 v2 v3 v5
du_regtag'45'branch_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'branch_1364 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_regtag'45'jump_1344
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatRegTagWF.regtag-ret
d_regtag'45'ret_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_regtag'45'ret_1386 ~v0 v1 ~v2 v3 = du_regtag'45'ret_1386 v1 v3
du_regtag'45'ret_1386 ::
  [Integer] -> T_RegTagWF_314 -> T_RegTagWF_314
du_regtag'45'ret_1386 v0 v1
  = case coe v0 of
      [] -> coe du_regtag'45'halt_420 (coe v1)
      (:) v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.flat-regtag-step
d_flat'45'regtag'45'step_1406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_314 -> T_RegTagWF_314
d_flat'45'regtag'45'step_1406 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v5 v6 v7
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v5 v6 v7
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v5 v6
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v6
               -> coe
                    du_regtag'45'jump_1344
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v6
               -> coe
                    du_regtag'45'branch_1364 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v6
               -> coe
                    du_regtag'45'branch_1364 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v6 v7
               -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v6
               -> coe
                    du_regtag'45'ret_1386
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v5
        -> coe
             d_regtag'45'abstract_908 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
