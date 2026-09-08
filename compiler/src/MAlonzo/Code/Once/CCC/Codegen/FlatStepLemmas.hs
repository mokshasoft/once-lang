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

module MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.FlatStepLemmas.≢⇒≡ᵇfalse
d_'8802''8658''8801''7495'false_12 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8658''8801''7495'false_12 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState
d_FlatState_40 a0 = ()
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.do-jump
d_do'45'jump_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_78 ~v0 = du_do'45'jump_78
du_do'45'jump_78 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_78
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.exec-flat
d_exec'45'flat_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_100 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3372 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fetch
d_fetch_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch_122 ~v0 = du_fetch_122
du_fetch_122 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch_122 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.find-label
d_find'45'label_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-go
d_fl'45'go_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_148 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-label-match
d_fl'45'label'45'match_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_156 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-exec-instr
d_flat'45'exec'45'instr_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-read-tag
d_flat'45'read'45'tag_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_170 ~v0 = du_flat'45'read'45'tag_170
du_flat'45'read'45'tag_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_170
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.label-of?
d_label'45'of'63'_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_220 ~v0 = du_label'45'of'63'_220
du_label'45'of'63'_220 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_220
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.shift
d_shift_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_250 ~v0 = du_shift_250
du_shift_250 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_250 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3128
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.sv-is-zero
d_sv'45'is'45'zero_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_290 ~v0 = du_sv'45'is'45'zero_290
du_sv'45'is'45'zero_290 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_290
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.tag-zf
d_tag'45'zf_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_292 ~v0 = du_tag'45'zf_292
du_tag'45'zf_292 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_292
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.falloc
d_falloc_308 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_308 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fclosure
d_fclosure_310 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_310 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.flink
d_flink_312 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_312 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.floc
d_floc_314 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_314 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fpc
d_fpc_316 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_316 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fret
d_fret_318 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_318 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps
d_FlatSteps_330 a0 a1 a2 a3 a4 = ()
data T_FlatSteps_330
  = C_'91''93'_336 |
    C__'8759'__346 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_FlatSteps_330
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_358 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-step1
d_flat'45'step1_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_330
d_flat'45'step1_382 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_flat'45'step1_382 v4 v5 v6
du_flat'45'step1_382 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_330
du_flat'45'step1_382 v0 v1 v2
  = coe
      C__'8759'__346 v0
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe C_'91''93'_336)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-label
d_flat'45'label_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_402 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-jmp
d_flat'45'jmp_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_416 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_430 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_450 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_470 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_490 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_510 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_534 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_606 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-shift
d_flm'45'shift_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_620 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_690 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-prefix
d_flm'45'prefix_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_704 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_798 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified
d_RunReified_822 a0 a1 a2 a3 = ()
data T_RunReified_822
  = C_reified_854 Integer Integer
                  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 T_FlatSteps_330
                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_842 :: T_RunReified_822 -> Integer
d_steps'45'len_842 v0
  = case coe v0 of
      C_reified_854 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_844 :: T_RunReified_822 -> Integer
d_rest'45'fuel_844 v0
  = case coe v0 of
      C_reified_854 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settle
d_settle_846 ::
  T_RunReified_822 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_846 v0
  = case coe v0 of
      C_reified_854 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.chain
d_chain_848 :: T_RunReified_822 -> T_FlatSteps_330
d_chain_848 v0
  = case coe v0 of
      C_reified_854 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settled
d_settled_850 ::
  T_RunReified_822 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_850 v0
  = case coe v0 of
      C_reified_854 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_852 ::
  T_RunReified_822 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_852 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.reify-run
d_reify'45'run_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RunReified_822
d_reify'45'run_862 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             C_reified_854 (0 :: Integer) (0 :: Integer) v3 (coe C_'91''93'_336)
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)) in
              coe
                (if coe v6
                   then coe
                          C_reified_854 (0 :: Integer) v1 v3 (coe C_'91''93'_336)
                          (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   else (let v7
                               = coe
                                   MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214 (coe v2)
                                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v3)) in
                         coe
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> let v9
                                         = d_reify'45'run_862
                                             (coe v0) (coe v5) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
                                                v0 v8 v2 v3)
                                             erased in
                                   coe
                                     (case coe v9 of
                                        C_reified_854 v10 v11 v12 v13 v14
                                          -> coe
                                               C_reified_854 (addInt (coe (1 :: Integer)) (coe v10))
                                               v11 v12
                                               (coe
                                                  C__'8759'__346 v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased)
                                                  v13)
                                               v14
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     C_reified_854 (0 :: Integer) v1 v3 (coe C_'91''93'_336)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-prefix
d_FlatSteps'45'prefix_966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_330 -> T_FlatSteps_330
d_FlatSteps'45'prefix_966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_FlatSteps'45'prefix_966 v7
du_FlatSteps'45'prefix_966 :: T_FlatSteps_330 -> T_FlatSteps_330
du_FlatSteps'45'prefix_966 v0
  = case coe v0 of
      C_'91''93'_336 -> coe C_'91''93'_336
      C__'8759'__346 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    C__'8759'__346 v4
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased)
                    (coe du_FlatSteps'45'prefix_966 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-reloc
d_FlatSteps'45'reloc_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_330 -> T_FlatSteps_330
d_FlatSteps'45'reloc_1008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_FlatSteps'45'reloc_1008 v7
du_FlatSteps'45'reloc_1008 :: T_FlatSteps_330 -> T_FlatSteps_330
du_FlatSteps'45'reloc_1008 v0
  = case coe v0 of
      C_'91''93'_336 -> coe C_'91''93'_336
      C__'8759'__346 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    C__'8759'__346 v4
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased)
                    (coe du_FlatSteps'45'reloc_1008 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_330 -> T_FlatSteps_330 -> T_FlatSteps_330
d_FlatSteps'45''43''43'_1046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_FlatSteps'45''43''43'_1046 v7 v8
du_FlatSteps'45''43''43'_1046 ::
  T_FlatSteps_330 -> T_FlatSteps_330 -> T_FlatSteps_330
du_FlatSteps'45''43''43'_1046 v0 v1
  = case coe v0 of
      C_'91''93'_336 -> coe v1
      C__'8759'__346 v5 v6 v7
        -> coe
             C__'8759'__346 v5 v6
             (coe du_FlatSteps'45''43''43'_1046 (coe v7) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps
d_chain'45'steps_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_330) -> T_FlatSteps_330
d_chain'45'steps_1066 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_chain'45'steps_1066 v3 v5
du_chain'45'steps_1066 ::
  Integer -> (Integer -> T_FlatSteps_330) -> T_FlatSteps_330
du_chain'45'steps_1066 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_336
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_FlatSteps'45''43''43'_1046 (coe v1 (0 :: Integer))
                (coe
                   du_chain'45'steps_1066 (coe v2)
                   (coe (\ v3 -> coe v1 (addInt (coe (1 :: Integer)) (coe v3))))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_1096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_330) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_1096 = erased
