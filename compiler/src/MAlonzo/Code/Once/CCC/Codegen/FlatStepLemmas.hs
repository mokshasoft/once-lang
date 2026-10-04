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
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.exec-flat
d_exec'45'flat_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3630 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fetch
d_fetch_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_128 ~v0 = du_fetch_128
du_fetch_128 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_128 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.find-label
d_find'45'label_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_146 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-go
d_fl'45'go_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_160 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-label-match
d_fl'45'label'45'match_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-exec-instr
d_flat'45'exec'45'instr_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-read-tag
d_flat'45'read'45'tag_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_182 ~v0 = du_flat'45'read'45'tag_182
du_flat'45'read'45'tag_182 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_182
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.label-of?
d_label'45'of'63'_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_242 ~v0 = du_label'45'of'63'_242
du_label'45'of'63'_242 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_242
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.shift
d_shift_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_272 ~v0 = du_shift_272
du_shift_272 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_272 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3374
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.sv-is-zero
d_sv'45'is'45'zero_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_312 ~v0 = du_sv'45'is'45'zero_312
du_sv'45'is'45'zero_312 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_312
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.tag-zf
d_tag'45'zf_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_314 ~v0 = du_tag'45'zf_314
du_tag'45'zf_314 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_314
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.falloc
d_falloc_332 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_332 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fclosure
d_fclosure_334 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_334 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.flink
d_flink_336 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_336 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.floc
d_floc_338 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_338 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fpc
d_fpc_340 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_340 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fret
d_fret_342 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_342 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps
d_FlatSteps_358 a0 a1 a2 a3 a4 = ()
data T_FlatSteps_358
  = C_'91''93'_364 |
    C__'8759'__374 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_FlatSteps_358
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.step-at
d_step'45'at_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FlatSteps_358 -> T_FlatSteps_358
d_step'45'at_388 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9
  = du_step'45'at_388 v5 v7 v9
du_step'45'at_388 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatSteps_358 -> T_FlatSteps_358
du_step'45'at_388 v0 v1 v2 = coe C__'8759'__374 v0 v1 v2
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_358 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_412 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-step1
d_flat'45'step1_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_358
d_flat'45'step1_436 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_flat'45'step1_436 v4 v5 v6
du_flat'45'step1_436 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_358
du_flat'45'step1_436 v0 v1 v2
  = coe
      C__'8759'__374 v0
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe C_'91''93'_364)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-label
d_flat'45'label_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_456 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-jmp
d_flat'45'jmp_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_470 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_484 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_504 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_524 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_544 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_564 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_588 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_660 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-shift
d_flm'45'shift_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_674 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_744 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-prefix
d_flm'45'prefix_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_758 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_852 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified
d_RunReified_876 a0 a1 a2 a3 = ()
data T_RunReified_876
  = C_reified_908 Integer Integer
                  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 T_FlatSteps_358
                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_896 :: T_RunReified_876 -> Integer
d_steps'45'len_896 v0
  = case coe v0 of
      C_reified_908 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_898 :: T_RunReified_876 -> Integer
d_rest'45'fuel_898 v0
  = case coe v0 of
      C_reified_908 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settle
d_settle_900 ::
  T_RunReified_876 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_900 v0
  = case coe v0 of
      C_reified_908 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.chain
d_chain_902 :: T_RunReified_876 -> T_FlatSteps_358
d_chain_902 v0
  = case coe v0 of
      C_reified_908 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settled
d_settled_904 ::
  T_RunReified_876 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_904 v0
  = case coe v0 of
      C_reified_908 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_906 ::
  T_RunReified_876 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_906 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.reify-run
d_reify'45'run_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RunReified_876
d_reify'45'run_916 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             C_reified_908 (0 :: Integer) (0 :: Integer) v3 (coe C_'91''93'_364)
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_432
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)) in
              coe
                (if coe v6
                   then coe
                          C_reified_908 (0 :: Integer) v1 v3 (coe C_'91''93'_364)
                          (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   else (let v7
                               = coe
                                   MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246 (coe v2)
                                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v3)) in
                         coe
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> let v9
                                         = d_reify'45'run_916
                                             (coe v0) (coe v5) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
                                                v0 v8 v2 v3)
                                             erased in
                                   coe
                                     (case coe v9 of
                                        C_reified_908 v10 v11 v12 v13 v14
                                          -> coe
                                               C_reified_908 (addInt (coe (1 :: Integer)) (coe v10))
                                               v11 v12
                                               (coe
                                                  C__'8759'__374 v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased)
                                                  v13)
                                               v14
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     C_reified_908 (0 :: Integer) v1 v3 (coe C_'91''93'_364)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-prefix
d_FlatSteps'45'prefix_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_358 -> T_FlatSteps_358
d_FlatSteps'45'prefix_1020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_FlatSteps'45'prefix_1020 v7
du_FlatSteps'45'prefix_1020 :: T_FlatSteps_358 -> T_FlatSteps_358
du_FlatSteps'45'prefix_1020 v0
  = case coe v0 of
      C_'91''93'_364 -> coe C_'91''93'_364
      C__'8759'__374 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    C__'8759'__374 v4
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased)
                    (coe du_FlatSteps'45'prefix_1020 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-reloc
d_FlatSteps'45'reloc_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_358 -> T_FlatSteps_358
d_FlatSteps'45'reloc_1062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_FlatSteps'45'reloc_1062 v7
du_FlatSteps'45'reloc_1062 :: T_FlatSteps_358 -> T_FlatSteps_358
du_FlatSteps'45'reloc_1062 v0
  = case coe v0 of
      C_'91''93'_364 -> coe C_'91''93'_364
      C__'8759'__374 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    C__'8759'__374 v4
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased)
                    (coe du_FlatSteps'45'reloc_1062 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-middle
d_FlatSteps'45'middle_1112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_358 -> T_FlatSteps_358
d_FlatSteps'45'middle_1112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_FlatSteps'45'middle_1112 v9
du_FlatSteps'45'middle_1112 :: T_FlatSteps_358 -> T_FlatSteps_358
du_FlatSteps'45'middle_1112 v0
  = coe
      du_FlatSteps'45'reloc_1062
      (coe du_FlatSteps'45'prefix_1020 (coe v0))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.link-block-steps
d_link'45'block'45'steps_1156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2326 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatSteps_358 -> T_FlatSteps_358
d_link'45'block'45'steps_1156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 ~v12 v13
  = du_link'45'block'45'steps_1156 v13
du_link'45'block'45'steps_1156 ::
  T_FlatSteps_358 -> T_FlatSteps_358
du_link'45'block'45'steps_1156 v0
  = coe du_FlatSteps'45'middle_1112 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_358 -> T_FlatSteps_358 -> T_FlatSteps_358
d_FlatSteps'45''43''43'_1192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_FlatSteps'45''43''43'_1192 v7 v8
du_FlatSteps'45''43''43'_1192 ::
  T_FlatSteps_358 -> T_FlatSteps_358 -> T_FlatSteps_358
du_FlatSteps'45''43''43'_1192 v0 v1
  = case coe v0 of
      C_'91''93'_364 -> coe v1
      C__'8759'__374 v5 v6 v7
        -> coe
             C__'8759'__374 v5 v6
             (coe du_FlatSteps'45''43''43'_1192 (coe v7) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps
d_chain'45'steps_1212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_358) -> T_FlatSteps_358
d_chain'45'steps_1212 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_chain'45'steps_1212 v3 v5
du_chain'45'steps_1212 ::
  Integer -> (Integer -> T_FlatSteps_358) -> T_FlatSteps_358
du_chain'45'steps_1212 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_364
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_FlatSteps'45''43''43'_1192 (coe v1 (0 :: Integer))
                (coe
                   du_chain'45'steps_1212 (coe v2)
                   (coe (\ v3 -> coe v1 (addInt (coe (1 :: Integer)) (coe v3))))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_358) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_1242 = erased
