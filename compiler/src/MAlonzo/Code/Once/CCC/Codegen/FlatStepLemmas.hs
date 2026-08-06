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
d_do'45'jump_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_64 ~v0 = du_do'45'jump_64
du_do'45'jump_64 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_64
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_504
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.exec-flat
d_exec'45'flat_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_1130 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fetch
d_fetch_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_106 ~v0 = du_fetch_106
du_fetch_106 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_106 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.find-label
d_find'45'label_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-go
d_fl'45'go_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_126 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_122 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-label-match
d_fl'45'label'45'match_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_126
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-exec-instr
d_flat'45'exec'45'instr_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-read-tag
d_flat'45'read'45'tag_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_140 ~v0 = du_flat'45'read'45'tag_140
du_flat'45'read'45'tag_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_140
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_114
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.label-of?
d_label'45'of'63'_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_168 ~v0 = du_label'45'of'63'_168
du_label'45'of'63'_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_168
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_118
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.sv-is-zero
d_sv'45'is'45'zero_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_198 ~v0 = du_sv'45'is'45'zero_198
du_sv'45'is'45'zero_198 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_198
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_100
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.tag-zf
d_tag'45'zf_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_200 ~v0 = du_tag'45'zf_200
du_tag'45'zf_200 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_200
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_102
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.falloc
d_falloc_216 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_216 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fclosure
d_fclosure_218 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_218 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.floc
d_floc_220 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_220 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fpc
d_fpc_222 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_222 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fret
d_fret_224 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_224 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps
d_FlatSteps_228 a0 a1 a2 a3 a4 = ()
data T_FlatSteps_228
  = C_'91''93'_234 |
    C__'8759'__244 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_FlatSteps_228
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_228 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_256 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-step1
d_flat'45'step1_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_228
d_flat'45'step1_280 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_flat'45'step1_280 v4 v5 v6
du_flat'45'step1_280 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_228
du_flat'45'step1_280 v0 v1 v2
  = coe
      C__'8759'__244 v0
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe C_'91''93'_234)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-label
d_flat'45'label_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_300 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-jmp
d_flat'45'jmp_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_314 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_328 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_348 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_368 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_388 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_408 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_432 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_504 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-shift
d_flm'45'shift_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_518 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_588 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-prefix
d_flm'45'prefix_602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_602 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_696 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified
d_RunReified_720 a0 a1 a2 a3 = ()
data T_RunReified_720
  = C_reified_752 Integer Integer
                  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 T_FlatSteps_228
                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_740 :: T_RunReified_720 -> Integer
d_steps'45'len_740 v0
  = case coe v0 of
      C_reified_752 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_742 :: T_RunReified_720 -> Integer
d_rest'45'fuel_742 v0
  = case coe v0 of
      C_reified_752 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settle
d_settle_744 ::
  T_RunReified_720 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_744 v0
  = case coe v0 of
      C_reified_752 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.chain
d_chain_746 :: T_RunReified_720 -> T_FlatSteps_228
d_chain_746 v0
  = case coe v0 of
      C_reified_752 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settled
d_settled_748 ::
  T_RunReified_720 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_748 v0
  = case coe v0 of
      C_reified_752 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_750 ::
  T_RunReified_720 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_750 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.reify-run
d_reify'45'run_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RunReified_720
d_reify'45'run_760 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             C_reified_752 (0 :: Integer) (0 :: Integer) v3 (coe C_'91''93'_234)
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)) in
              coe
                (if coe v6
                   then coe
                          C_reified_752 (0 :: Integer) v1 v3 (coe C_'91''93'_234)
                          (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   else (let v7
                               = coe
                                   MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210 (coe v2)
                                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v3)) in
                         coe
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> let v9
                                         = d_reify'45'run_760
                                             (coe v0) (coe v5) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076
                                                v0 v8 v2 v3)
                                             erased in
                                   coe
                                     (case coe v9 of
                                        C_reified_752 v10 v11 v12 v13 v14
                                          -> coe
                                               C_reified_752 (addInt (coe (1 :: Integer)) (coe v10))
                                               v11 v12
                                               (coe
                                                  C__'8759'__244 v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased)
                                                  v13)
                                               v14
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     C_reified_752 (0 :: Integer) v1 v3 (coe C_'91''93'_234)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatSteps_228 -> T_FlatSteps_228 -> T_FlatSteps_228
d_FlatSteps'45''43''43'_860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_FlatSteps'45''43''43'_860 v7 v8
du_FlatSteps'45''43''43'_860 ::
  T_FlatSteps_228 -> T_FlatSteps_228 -> T_FlatSteps_228
du_FlatSteps'45''43''43'_860 v0 v1
  = case coe v0 of
      C_'91''93'_234 -> coe v1
      C__'8759'__244 v5 v6 v7
        -> coe
             C__'8759'__244 v5 v6
             (coe du_FlatSteps'45''43''43'_860 (coe v7) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps
d_chain'45'steps_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_228) -> T_FlatSteps_228
d_chain'45'steps_880 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_chain'45'steps_880 v3 v5
du_chain'45'steps_880 ::
  Integer -> (Integer -> T_FlatSteps_228) -> T_FlatSteps_228
du_chain'45'steps_880 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_234
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_FlatSteps'45''43''43'_860 (coe v1 (0 :: Integer))
                (coe
                   du_chain'45'steps_880 (coe v2)
                   (coe (\ v3 -> coe v1 (addInt (coe (1 :: Integer)) (coe v3))))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer -> T_FlatSteps_228) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_910 = erased
