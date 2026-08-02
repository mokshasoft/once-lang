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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLoc_26 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'lea'45'indexed'45'via_54 ~v0
  = du_exec'45'lea'45'indexed'45'via_54
du_exec'45'lea'45'indexed'45'via_54 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'lea'45'indexed'45'via_54
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1520
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'suc'45'via'45'resolved_60 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_60
du_exec'45'load'45'suc'45'via'45'resolved_60 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'suc'45'via'45'resolved_60
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1532
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'via'45'resolved_62 ~v0
  = du_exec'45'load'45'via'45'resolved_62
du_exec'45'load'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'via'45'resolved_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1494
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'with'45'value_64 ~v0
  = du_exec'45'load'45'with'45'value_64
du_exec'45'load'45'with'45'value_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'with'45'value_64
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1482
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'store'45'suc'45'via'45'resolved_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1544
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'store'45'via'45'resolved_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1506
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.BodyRunner
d_BodyRunner_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_78 = erased
-- Once.CCC.Machine.FlatRegTagWF._.exec-abstract
d_exec'45'abstract_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2822
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_94
du_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_94
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2512
-- Once.CCC.Machine.FlatRegTagWF._.exec-loop-run
d_exec'45'loop'45'run_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_98 ~v0 = du_exec'45'loop'45'run_98
du_exec'45'loop'45'run_98 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_98
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2760
-- Once.CCC.Machine.FlatRegTagWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_104 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_104
du_exec'45'restore'45'input'45'with'45'value_104 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2524
-- Once.CCC.Machine.FlatRegTagWF._.exec-trace
d_exec'45'trace_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2818 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_loop'45'reanchor'45'alloc_140 ~v0
  = du_loop'45'reanchor'45'alloc_140
du_loop'45'reanchor'45'alloc_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_loop'45'reanchor'45'alloc_140
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2754
-- Once.CCC.Machine.FlatRegTagWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_loop'45'reanchor'45'loc_142 ~v0 = du_loop'45'reanchor'45'loc_142
du_loop'45'reanchor'45'loc_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_loop'45'reanchor'45'loc_142
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2748
-- Once.CCC.Machine.FlatRegTagWF._.FlatState
d_FlatState_164 a0 = ()
-- Once.CCC.Machine.FlatRegTagWF._.do-branch
d_do'45'branch_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_164 (coe v0)
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
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_156
-- Once.CCC.Machine.FlatRegTagWF._.flat-exec-instr
d_flat'45'exec'45'instr_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_210 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_262
      (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.falloc
d_falloc_250 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_250 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.floc
d_floc_252 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_252 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF._.FlatState.fpc
d_fpc_254 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_254 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.IsTag
d_IsTag_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTag_256 = erased
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF
d_RegTagWF_264 a0 a1 = ()
data T_RegTagWF_264
  = C_mkRegTagWF_276 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.scratch-tag
d_scratch'45'tag_272 ::
  T_RegTagWF_264 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'tag_272 v0
  = case coe v0 of
      C_mkRegTagWF_276 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.RegTagWF.count-tag
d_count'45'tag_274 ::
  T_RegTagWF_264 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'tag_274 v0
  = case coe v0 of
      C_mkRegTagWF_276 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.IsTagP
d_IsTagP_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_IsTagP_278 = erased
-- Once.CCC.Machine.FlatRegTagWF.is-tag-P
d_is'45'tag'45'P_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_is'45'tag'45'P_282 ~v0 ~v1 v2 = du_is'45'tag'45'P_282 v2
du_is'45'tag'45'P_282 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_is'45'tag'45'P_282 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatRegTagWF.sv-succ-tag
d_sv'45'succ'45'tag_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'succ'45'tag_288 ~v0 ~v1 v2 = du_sv'45'succ'45'tag_288 v2
du_sv'45'succ'45'tag_288 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'succ'45'tag_288 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (1 :: Integer)) (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.sv-pred-tag
d_sv'45'pred'45'tag_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sv'45'pred'45'tag_294 ~v0 ~v1 v2 = du_sv'45'pred'45'tag_294 v2
du_sv'45'pred'45'tag_294 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sv'45'pred'45'tag_294 v0
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
d_regtag'45'write'45'other_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'other_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'other_304 v6
du_regtag'45'write'45'other_304 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'other_304 v0
  = coe
      C_mkRegTagWF_276
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_272 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_274 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in1
d_regtag'45'write'45'in1_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'in1_322 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in1_322 v3
du_regtag'45'write'45'in1_322 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'in1_322 v0
  = coe du_regtag'45'write'45'other_304 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-in2
d_regtag'45'write'45'in2_334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'in2_334 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'in2_334 v3
du_regtag'45'write'45'in2_334 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'in2_334 v0
  = coe du_regtag'45'write'45'other_304 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-out
d_regtag'45'write'45'out_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'out_346 ~v0 ~v1 ~v2 v3
  = du_regtag'45'write'45'out_346 v3
du_regtag'45'write'45'out_346 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'out_346 v0
  = coe du_regtag'45'write'45'other_304 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-transport
d_regtag'45'transport_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'transport_358 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_regtag'45'transport_358 v5
du_regtag'45'transport_358 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'transport_358 v0
  = coe
      C_mkRegTagWF_276
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_272 (coe v0)))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_274 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-halt
d_regtag'45'halt_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'halt_370 ~v0 ~v1 v2 = du_regtag'45'halt_370 v2
du_regtag'45'halt_370 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'halt_370 v0 = coe du_regtag'45'transport_358 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.NonCounter
d_NonCounter_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> ()
d_NonCounter_376 = erased
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc
d_regtag'45'write'45'nc_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'nc_384 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_regtag'45'write'45'nc_384 v2 v5
du_regtag'45'write'45'nc_384 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'nc_384 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_358 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-nc-halt
d_regtag'45'write'45'nc'45'halt_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'nc'45'halt_412 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_regtag'45'write'45'nc'45'halt_412 v2 v6
du_regtag'45'write'45'nc'45'halt_412 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'nc'45'halt_412 v0 v1
  = coe seq (coe v0) (coe du_regtag'45'transport_358 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-scratch
d_regtag'45'set'45'scratch_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'set'45'scratch_442 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'scratch_442 v3 v4
du_regtag'45'set'45'scratch_442 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'set'45'scratch_442 v0 v1
  = coe C_mkRegTagWF_276 (coe v0) (coe d_count'45'tag_274 (coe v1))
-- Once.CCC.Machine.FlatRegTagWF.regtag-set-count
d_regtag'45'set'45'count_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'set'45'count_456 ~v0 ~v1 ~v2 v3 v4
  = du_regtag'45'set'45'count_456 v3 v4
du_regtag'45'set'45'count_456 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'set'45'count_456 v0 v1
  = coe C_mkRegTagWF_276 (coe d_scratch'45'tag_272 (coe v1)) (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-stack-slot
d_regtag'45'stack'45'slot_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Integer -> T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'stack'45'slot_470 ~v0 ~v1 ~v2 v3
  = du_regtag'45'stack'45'slot_470 v3
du_regtag'45'stack'45'slot_470 :: T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'stack'45'slot_470 v0
  = coe du_regtag'45'transport_358 (coe v0)
-- Once.CCC.Machine.FlatRegTagWF.regtag-write-loc
d_regtag'45'write'45'loc_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'write'45'loc_484 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'write'45'loc_484 v2 v3 v4
du_regtag'45'write'45'loc_484 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'write'45'loc_484 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe du_regtag'45'transport_358 (coe v2)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
               -> coe seq (coe v4) (coe du_regtag'45'transport_358 (coe v2))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
               -> coe du_regtag'45'transport_358 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
               -> coe du_regtag'45'transport_358 (coe v2)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
               -> coe du_regtag'45'transport_358 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-value
d_regtag'45'load'45'value_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'load'45'value_546 ~v0 ~v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'value_546 v2 v4 v5
du_regtag'45'load'45'value_546 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'load'45'value_546 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'nc_384 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-resolved
d_regtag'45'load'45'resolved_568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'load'45'resolved_568 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'resolved_568 v1 v2 v4 v5
du_regtag'45'load'45'resolved_568 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'load'45'resolved_568 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_546 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe v4))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-load-suc-resolved
d_regtag'45'load'45'suc'45'resolved_592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'load'45'suc'45'resolved_592 ~v0 v1 v2 ~v3 v4 v5
  = du_regtag'45'load'45'suc'45'resolved_592 v1 v2 v4 v5
du_regtag'45'load'45'suc'45'resolved_592 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'load'45'suc'45'resolved_592 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_regtag'45'load'45'value_546 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-resolved
d_regtag'45'store'45'resolved_616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'store'45'resolved_616 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'resolved_616 v2 v3 v4
du_regtag'45'store'45'resolved_616 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'store'45'resolved_616 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_regtag'45'write'45'loc_484 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-store-suc-resolved
d_regtag'45'store'45'suc'45'resolved_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'store'45'suc'45'resolved_634 ~v0 ~v1 v2 v3 v4
  = du_regtag'45'store'45'suc'45'resolved_634 v2 v3 v4
du_regtag'45'store'45'suc'45'resolved_634 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'store'45'suc'45'resolved_634 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_regtag'45'write'45'loc_484
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v3))
             (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-lea-indexed
d_regtag'45'lea'45'indexed_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'lea'45'indexed_652 ~v0 ~v1 v2 ~v3 v4
  = du_regtag'45'lea'45'indexed_652 v2 v4
du_regtag'45'lea'45'indexed_652 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'lea'45'indexed_652 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-out
d_regtag'45'slot'45'load'45'out_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'slot'45'load'45'out_670 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'out_670 v1 v4
du_regtag'45'slot'45'load'45'out_670 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'slot'45'load'45'out_670 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-slot-load-in1
d_regtag'45'slot'45'load'45'in1_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'slot'45'load'45'in1_692 ~v0 v1 ~v2 ~v3 v4
  = du_regtag'45'slot'45'load'45'in1_692 v1 v4
du_regtag'45'slot'45'load'45'in1_692 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'slot'45'load'45'in1_692 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run
d_regtag'45'loop'45'run_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_RegTagWF_264 -> T_RegTagWF_264) ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'loop'45'run_720 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe du_regtag'45'halt_370 (coe v6)
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v8
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v3) in
              coe
                (if coe v8
                   then coe v6
                   else (let v9
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_150
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v3)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_734 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v10
                                -> case coe v10 of
                                     0 -> coe v6
                                     _ -> coe
                                            d_regtag'45'loop'45'run'45'go_734 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v10 v11 v12
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_734 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v10
                                -> coe
                                     d_regtag'45'loop'45'run'45'go_734 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatRegTagWF.regtag-loop-run-go
d_regtag'45'loop'45'run'45'go_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_RegTagWF_264 -> T_RegTagWF_264) ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'loop'45'run'45'go_734 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_regtag'45'loop'45'run_720 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2748
         (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v3 v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2754
         (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1 v3 v4)))
      (coe v5) (coe du_regtag'45'transport_358 (coe v5 v3 v4 v6))
-- Once.CCC.Machine.FlatRegTagWF.regtag-abstract
d_regtag'45'abstract_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'abstract_870 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             du_regtag'45'load'45'resolved_568 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             du_regtag'45'load'45'suc'45'resolved_592 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_670
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v5
        -> coe
             du_regtag'45'write'45'loc_484
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             du_regtag'45'store'45'resolved_616
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             du_regtag'45'store'45'suc'45'resolved_634
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v5
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v5
        -> coe
             du_regtag'45'slot'45'load'45'in1_692
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v5
        -> coe du_regtag'45'stack'45'slot_470 (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v5
        -> coe du_regtag'45'stack'45'slot_470 (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v5
        -> coe du_regtag'45'stack'45'slot_470 (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v5
        -> coe
             du_regtag'45'write'45'loc_484
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe v3))
                (coe v5))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v5
        -> coe
             du_regtag'45'slot'45'load'45'out_670
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc'45'halt_412
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v5 v6 v7
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v5
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v5
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v5 v6
        -> coe
             d_regtag'45'case_890 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2732
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v5
        -> coe
             du_regtag'45'write'45'nc_384
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v5
        -> coe
             d_regtag'45'loop'45'run_720 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2818 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_regtag'45'trace_878 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_508
               -> coe
                    du_regtag'45'set'45'scratch_442
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_510
               -> coe
                    du_regtag'45'set'45'scratch_442
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_512
               -> coe
                    du_regtag'45'set'45'scratch_442
                    (coe du_sv'45'pred'45'tag_294 (coe d_scratch'45'tag_272 (coe v4)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_514
               -> coe
                    du_regtag'45'set'45'scratch_442 (coe d_count'45'tag_274 (coe v4))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_516
               -> coe
                    du_regtag'45'set'45'count_456
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       erased)
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_518
               -> coe
                    du_regtag'45'set'45'count_456
                    (coe du_sv'45'succ'45'tag_288 (coe d_count'45'tag_274 (coe v4)))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v5
        -> coe
             du_regtag'45'lea'45'indexed_652
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1516
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                         (coe v3))
                      (coe v5))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-trace
d_regtag'45'trace_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'trace_878 v0 v1 v2 v3 v4
  = case coe v1 of
      [] -> coe v4
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v2) in
           coe
             (if coe v7
                then coe v4
                else coe
                       d_regtag'45'trace_878 (coe v0) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                             (coe v0) (coe v5) (coe v2) (coe v3)))
                       (coe
                          d_regtag'45'abstract_870 (coe v0) (coe v5) (coe v2) (coe v3)
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-case
d_regtag'45'case_890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'case_890 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v8
               -> coe du_regtag'45'halt_370 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v8
               -> case coe v8 of
                    0 -> coe
                           d_regtag'45'trace_878 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_regtag'45'trace_878 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v8 v9 v10
               -> coe du_regtag'45'halt_370 (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v8
               -> coe du_regtag'45'halt_370 (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.FlatRegTag
d_FlatRegTag_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_1270 = erased
-- Once.CCC.Machine.FlatRegTagWF.flat-scratch-is-tag
d_flat'45'scratch'45'is'45'tag_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'scratch'45'is'45'tag_1278 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'scratch'45'is'45'tag_1278 v3
du_flat'45'scratch'45'is'45'tag_1278 :: T_RegTagWF_264 -> AgdaAny
du_flat'45'scratch'45'is'45'tag_1278 v0
  = coe
      du_is'45'tag'45'P_282
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_scratch'45'tag_272 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.flat-count-is-tag
d_flat'45'count'45'is'45'tag_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_RegTagWF_264 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_flat'45'count'45'is'45'tag_1292 ~v0 ~v1 ~v2 v3 ~v4
  = du_flat'45'count'45'is'45'tag_1292 v3
du_flat'45'count'45'is'45'tag_1292 :: T_RegTagWF_264 -> AgdaAny
du_flat'45'count'45'is'45'tag_1292 v0
  = coe
      du_is'45'tag'45'P_282
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_count'45'tag_274 (coe v0)))
         erased)
-- Once.CCC.Machine.FlatRegTagWF.regtag-jump
d_regtag'45'jump_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'jump_1306 ~v0 v1 ~v2 v3 = du_regtag'45'jump_1306 v1 v3
du_regtag'45'jump_1306 ::
  Maybe Integer -> T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'jump_1306 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_regtag'45'halt_370 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatRegTagWF.regtag-branch
d_regtag'45'branch_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_regtag'45'branch_1326 v0 v1 v2 v3 ~v4 v5
  = du_regtag'45'branch_1326 v0 v1 v2 v3 v5
du_regtag'45'branch_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_RegTagWF_264 -> T_RegTagWF_264
du_regtag'45'branch_1326 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_regtag'45'jump_1306
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatRegTagWF.flat-regtag-step
d_flat'45'regtag'45'step_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_RegTagWF_264 -> T_RegTagWF_264
d_flat'45'regtag'45'step_1350 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v5 v6 v7
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v5 v6 v7
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v5 v6
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v6
               -> coe
                    du_regtag'45'jump_1306
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v6
               -> coe
                    du_regtag'45'branch_1326 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v6
               -> coe
                    du_regtag'45'branch_1326 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_80
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_92
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v5
        -> coe
             d_regtag'45'abstract_870 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
