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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_32 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_810 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'lea'45'indexed'45'via_60 ~v0
  = du_exec'45'lea'45'indexed'45'via_60
du_exec'45'lea'45'indexed'45'via_60 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'lea'45'indexed'45'via_60
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1490
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_66 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_66
du_exec'45'load'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_66
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1502
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'via'45'resolved_68 ~v0
  = du_exec'45'load'45'via'45'resolved_68
du_exec'45'load'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'via'45'resolved_68
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1464
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'with'45'value_70 ~v0
  = du_exec'45'load'45'with'45'value_70
du_exec'45'load'45'with'45'value_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'with'45'value_70
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1452
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1514
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'via'45'resolved_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1476
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.BodyRunner
d_BodyRunner_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_84 = erased
-- Once.CCC.Machine.FlatRegTagWF._.exec-abstract
d_exec'45'abstract_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_90 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_94 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2870
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_100 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_100
du_exec'45'load'45'from'45'slot'45'with'45'value_100 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_100
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2550
-- Once.CCC.Machine.FlatRegTagWF._.exec-loop-run
d_exec'45'loop'45'run_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_104 ~v0 = du_exec'45'loop'45'run_104
du_exec'45'loop'45'run_104 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2798
-- Once.CCC.Machine.FlatRegTagWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_110 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_110
du_exec'45'restore'45'input'45'with'45'value_110 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_110
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2562
-- Once.CCC.Machine.FlatRegTagWF._.exec-trace
d_exec'45'trace_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_loop'45'reanchor'45'alloc_148 ~v0
  = du_loop'45'reanchor'45'alloc_148
du_loop'45'reanchor'45'alloc_148 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_loop'45'reanchor'45'alloc_148
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2792
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_loop'45'reanchor'45'loc_150 ~v0 = du_loop'45'reanchor'45'loc_150
du_loop'45'reanchor'45'loc_150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_loop'45'reanchor'45'loc_150
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2786
-- Once.CCC.Machine.FlatRegTagWF._.CallPost
d_CallPost_172 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatRegTagWF._.FlatState
d_FlatState_174 a0 = ()
-- Once.CCC.Machine.FlatRegTagWF._.do-branch
d_do'45'branch_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_194 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_766 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.do-call
d_do'45'call_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_198 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1168 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.do-jump
d_do'45'jump_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_212 ~v0 = du_do'45'jump_212
du_do'45'jump_212 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_212
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750
-- Once.CCC.Machine.FlatRegTagWF._.do-ret
d_do'45'ret_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_214 ~v0 = du_do'45'ret_214
du_do'45'ret_214 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_214
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968
-- Once.CCC.Machine.FlatRegTagWF._.flat-exec-instr
d_flat'45'exec'45'instr_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_294 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.falloc
d_falloc_442 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_442 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fclosure
d_fclosure_444 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_444 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.flink
d_flink_446 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_446 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.floc
d_floc_448 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_448 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fpc
d_fpc_450 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_450 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fret
d_fret_452 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_452 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.IsTag
d_IsTag_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_IsTag_462 = erased
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF
d_RegTagWF_470 a0 a1 = ()
data T_RegTagWF_470
  = C_mkRegTagWF_482 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.scratch-tag
d_scratch'45'tag_478 ::
  T_RegTagWF_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'tag_478 v0
  = case coe v0 of
      C_mkRegTagWF_482 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.count-tag
d_count'45'tag_480 ::
  T_RegTagWF_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'tag_480 v0
  = case coe v0 of
      C_mkRegTagWF_482 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.IsTagP
d_IsTagP_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_IsTagP_484 = erased
-- Once.CCC.Machine.FlatRegTagWF.is-tag-P
d_is'45'tag'45'P_488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_is'45'tag'45'P_488 ~v0 ~v1 v2 = du_is'45'tag'45'P_488 v2
du_is'45'tag'45'P_488 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_is'45'tag'45'P_488 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatRegTagWF.sv-succ-tag
d_sv'45'succ'45'tag_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'succ'45'tag_494 ~v0 ~v1 v2 = du_sv'45'succ'45'tag_494 v2
du_sv'45'succ'45'tag_494 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'succ'45'tag_494 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (1 :: Integer)) (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.sv-pred-tag
d_sv'45'pred'45'tag_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'pred'45'tag_500 ~v0 ~v1 v2 = du_sv'45'pred'45'tag_500 v2
du_sv'45'pred'45'tag_500 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'pred'45'tag_500 v0
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
d_regtag'45'write'45'other_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'other_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'other_510 v6
du_regtag'45'write'45'other_510 :: T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'other_510 v0
  = coe
      C_mkRegTagWF_482
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_478 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_480 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in1
d_regtag'45'write'45'in1_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'in1_528 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in1_528 v3
du_regtag'45'write'45'in1_528 :: T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'in1_528 v0
  = coe du_regtag'45'write'45'other_510 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-out
d_regtag'45'write'45'out_540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'out_540 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'out_540 v3
du_regtag'45'write'45'out_540 :: T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'out_540 v0
  = coe du_regtag'45'write'45'other_510 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-transport
d_regtag'45'transport_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'transport_552 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_regtag'45'transport_552 v5
du_regtag'45'transport_552 :: T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'transport_552 v0
  = coe
      C_mkRegTagWF_482
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_478 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_480 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-halt
d_regtag'45'halt_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'halt_564 ~v0 ~v1 v2 = du_regtag'45'halt_564 v2
du_regtag'45'halt_564 :: T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'halt_564 v0 = coe du_regtag'45'transport_552 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.NonCounter
d_NonCounter_570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> ()
d_NonCounter_570 = erased
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc
d_regtag'45'write'45'nc_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'nc_578 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_regtag'45'write'45'nc_578 v2 v5
du_regtag'45'write'45'nc_578 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'nc_578 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_552 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc-halt
d_regtag'45'write'45'nc'45'halt_600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool -> T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'nc'45'halt_600 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'nc'45'halt_600 v2 v6
du_regtag'45'write'45'nc'45'halt_600 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'nc'45'halt_600 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_552 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-scratch
d_regtag'45'set'45'scratch_622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'set'45'scratch_622 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'scratch_622 v3 v4
du_regtag'45'set'45'scratch_622 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'set'45'scratch_622 v0 v1
  = coe C_mkRegTagWF_482 (coe v0) (coe d_count'45'tag_480 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-count
d_regtag'45'set'45'count_636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'set'45'count_636 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'count_636 v3 v4
du_regtag'45'set'45'count_636 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'set'45'count_636 v0 v1
  = coe C_mkRegTagWF_482 (coe d_scratch'45'tag_478 (coe v1)) (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-loc
d_regtag'45'write'45'loc_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'write'45'loc_652 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'write'45'loc_652 v2 v3 v4
du_regtag'45'write'45'loc_652 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'write'45'loc_652 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe du_regtag'45'transport_552 (coe v2)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v4
               -> coe seq (coe v4) (coe du_regtag'45'transport_552 (coe v2))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v4
               -> coe du_regtag'45'transport_552 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v4 v5 v6
               -> coe du_regtag'45'transport_552 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v4
               -> coe du_regtag'45'transport_552 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-value
d_regtag'45'load'45'value_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'load'45'value_714 ~v0 ~v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'value_714 v2 v4 v5
du_regtag'45'load'45'value_714 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'load'45'value_714 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'nc_578 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-resolved
d_regtag'45'load'45'resolved_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'load'45'resolved_736 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'resolved_736 v1 v2 v4 v5
du_regtag'45'load'45'resolved_736 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'load'45'resolved_736 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_714 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe v4))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-suc-resolved
d_regtag'45'load'45'suc'45'resolved_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'load'45'suc'45'resolved_760 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'suc'45'resolved_760 v1 v2 v4 v5
du_regtag'45'load'45'suc'45'resolved_760 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'load'45'suc'45'resolved_760 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_714 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-resolved
d_regtag'45'store'45'resolved_784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'store'45'resolved_784 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'resolved_784 v2 v3 v4
du_regtag'45'store'45'resolved_784 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'store'45'resolved_784 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'loc_652 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-suc-resolved
d_regtag'45'store'45'suc'45'resolved_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'store'45'suc'45'resolved_802 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'suc'45'resolved_802 v2 v3 v4
du_regtag'45'store'45'suc'45'resolved_802 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'store'45'suc'45'resolved_802 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_regtag'45'write'45'loc_652
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
             (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-lea-indexed
d_regtag'45'lea'45'indexed_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'lea'45'indexed_820 ~v0 ~v1 v2 ~v3 v4
  = du_regtag'45'lea'45'indexed_820 v2 v4
du_regtag'45'lea'45'indexed_820 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'lea'45'indexed_820 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-out
d_regtag'45'slot'45'load'45'out_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'slot'45'load'45'out_838 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'out_838 v1 v4
du_regtag'45'slot'45'load'45'out_838 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'slot'45'load'45'out_838 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-in1
d_regtag'45'slot'45'load'45'in1_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'slot'45'load'45'in1_860 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'in1_860 v1 v4
du_regtag'45'slot'45'load'45'in1_860 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'slot'45'load'45'in1_860 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run
d_regtag'45'loop'45'run_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_RegTagWF_470 -> T_RegTagWF_470) ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'loop'45'run_888 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe du_regtag'45'halt_564 (coe v6)
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v8
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v3) in
              coe
                (if coe v8
                   then coe v6
                   else (let v9
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_140
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v3)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_902 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v10
                                -> case coe v10 of
                                     0 -> coe v6
                                     _ -> coe
                                            d_regtag'45'loop'45'run'45'go_902 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v10 v11 v12
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_902 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_902 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run-go
d_regtag'45'loop'45'run'45'go_902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_RegTagWF_470 -> T_RegTagWF_470) ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'loop'45'run'45'go_902 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_regtag'45'loop'45'run_888 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2786
         (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v3 v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2792
         (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1 v3 v4)))
      (coe v5) (coe du_regtag'45'transport_552 (coe v5 v3 v4 v6))
-- Once.CCC.Machine.FlatRegTagWF.regtag-abstract
d_regtag'45'abstract_1038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'abstract_1038 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             du_regtag'45'load'45'resolved_736 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             du_regtag'45'load'45'suc'45'resolved_760 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_838
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v5
        -> coe
             du_regtag'45'write'45'loc_652
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             du_regtag'45'store'45'resolved_784
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             du_regtag'45'store'45'suc'45'resolved_802
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v5
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             du_regtag'45'slot'45'load'45'in1_860
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v5
        -> coe
             du_regtag'45'write'45'loc_652
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_838
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc'45'halt_600
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v5
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v5
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             d_regtag'45'case_1058 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2770
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             du_regtag'45'write'45'nc_578
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             d_regtag'45'loop'45'run_888 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_regtag'45'trace_1046 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
               -> coe
                    du_regtag'45'set'45'scratch_622
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
               -> coe
                    du_regtag'45'set'45'scratch_622
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
               -> coe
                    du_regtag'45'set'45'scratch_622
                    (coe du_sv'45'pred'45'tag_500 (coe d_scratch'45'tag_478 (coe v4)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
               -> coe
                    du_regtag'45'set'45'scratch_622 (coe d_count'45'tag_480 (coe v4))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
               -> coe
                    du_regtag'45'set'45'count_636
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
               -> coe
                    du_regtag'45'set'45'count_636
                    (coe du_sv'45'succ'45'tag_494 (coe d_count'45'tag_480 (coe v4)))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v5
        -> coe
             du_regtag'45'lea'45'indexed_820
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1486
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                         (coe v3))
                      (coe v5))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-trace
d_regtag'45'trace_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'trace_1046 v0 v1 v2 v3 v4
  = case coe v1 of
      [] -> coe v4
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v2) in
           coe
             (if coe v7
                then coe v4
                else coe
                       d_regtag'45'trace_1046 (coe v0) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          d_regtag'45'abstract_1038 (coe v0) (coe v5) (coe v2) (coe v3)
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-case
d_regtag'45'case_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'case_1058 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v8
               -> coe du_regtag'45'halt_564 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v8
               -> case coe v8 of
                    0 -> coe
                           d_regtag'45'trace_1046 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_regtag'45'trace_1046 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v8 v9 v10
               -> coe du_regtag'45'halt_564 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v8
               -> coe du_regtag'45'halt_564 (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.FlatRegTag
d_FlatRegTag_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_1426 = erased
-- Once.CCC.Machine.FlatRegTagWF.flat-scratch-is-tag
d_flat'45'scratch'45'is'45'tag_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'scratch'45'is'45'tag_1434 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'scratch'45'is'45'tag_1434 v3
du_flat'45'scratch'45'is'45'tag_1434 :: T_RegTagWF_470 -> AgdaAny
du_flat'45'scratch'45'is'45'tag_1434 v0
  = coe
      du_is'45'tag'45'P_488
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_478 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.flat-count-is-tag
d_flat'45'count'45'is'45'tag_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_RegTagWF_470 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'count'45'is'45'tag_1448 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'count'45'is'45'tag_1448 v3
du_flat'45'count'45'is'45'tag_1448 :: T_RegTagWF_470 -> AgdaAny
du_flat'45'count'45'is'45'tag_1448 v0
  = coe
      du_is'45'tag'45'P_488
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_480 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-jump
d_regtag'45'jump_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'jump_1462 ~v0 v1 ~v2 v3 = du_regtag'45'jump_1462 v1 v3
du_regtag'45'jump_1462 ::
  Maybe Integer -> T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'jump_1462 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_564 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-branch
d_regtag'45'branch_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'branch_1482 v0 v1 v2 v3 ~v4 v5
  = du_regtag'45'branch_1482 v0 v1 v2 v3 v5
du_regtag'45'branch_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'branch_1482 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_regtag'45'jump_1462
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatRegTagWF.regtag-ret
d_regtag'45'ret_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'ret_1504 ~v0 v1 ~v2 v3 = du_regtag'45'ret_1504 v1 v3
du_regtag'45'ret_1504 ::
  [Integer] -> T_RegTagWF_470 -> T_RegTagWF_470
du_regtag'45'ret_1504 v0 v1
  = case coe v0 of
      [] -> coe du_regtag'45'halt_564 (coe v1)
      (:) v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-call
d_regtag'45'call_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_regtag'45'call_1522 v0 v1 v2 v3
  = coe
      du_go_1534 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196 (coe v0)
         (coe v1) (coe v2))
-- Once.CCC.Machine.FlatRegTagWF._.go
d_go_1534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 ->
  T_RegTagWF_470
d_go_1534 ~v0 ~v1 ~v2 v3 v4 = du_go_1534 v3 v4
du_go_1534 ::
  T_RegTagWF_470 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 ->
  T_RegTagWF_470
du_go_1534 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'halt_1184
        -> coe du_regtag'45'halt_564 (coe v0)
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'enter_1190 v2 v3
        -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.flat-regtag-step
d_flat'45'regtag'45'step_1560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_RegTagWF_470 -> T_RegTagWF_470
d_flat'45'regtag'45'step_1560 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe d_regtag'45'call_1522 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v5 v6 v7
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v5 v6 v7
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v6
               -> coe
                    du_regtag'45'jump_1462
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v6
               -> coe
                    du_regtag'45'branch_1482 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212 v6
               -> coe
                    du_regtag'45'branch_1482 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v6 v7
               -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v6
               -> coe
                    du_regtag'45'ret_1504
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v5
        -> coe
             d_regtag'45'abstract_1038 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
