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
d_FlatState_38 a0 = ()
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.do-jump
d_do'45'jump_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_do'45'jump_48 ~v0 = du_do'45'jump_48
du_do'45'jump_48 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
du_do'45'jump_48
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_150
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.exec-flat
d_exec'45'flat_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_exec'45'flat_50 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_200 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fetch
d_fetch_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060
d_fetch_68 ~v0 = du_fetch_68
du_fetch_68 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060
du_fetch_68 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_142
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.find-label
d_find'45'label_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer -> Maybe Integer
d_find'45'label_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_136 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-go
d_fl'45'go_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_78 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_94 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-label-match
d_fl'45'label'45'match_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_80 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_96
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-exec-instr
d_flat'45'exec'45'instr_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_flat'45'exec'45'instr_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_174
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-read-tag
d_flat'45'read'45'tag_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78
d_flat'45'read'45'tag_86 ~v0 = du_flat'45'read'45'tag_86
du_flat'45'read'45'tag_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78
du_flat'45'read'45'tag_86
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_86
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.label-of?
d_label'45'of'63'_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  Maybe Integer
d_label'45'of'63'_96 ~v0 = du_label'45'of'63'_96
du_label'45'of'63'_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  Maybe Integer
du_label'45'of'63'_96
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_90
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.sv-is-zero
d_sv'45'is'45'zero_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 -> Bool
d_sv'45'is'45'zero_104 ~v0 = du_sv'45'is'45'zero_104
du_sv'45'is'45'zero_104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 -> Bool
du_sv'45'is'45'zero_104
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_72
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.tag-zf
d_tag'45'zf_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 -> Bool
d_tag'45'zf_106 ~v0 = du_tag'45'zf_106
du_tag'45'zf_106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 -> Bool
du_tag'45'zf_106
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_74
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.falloc
d_falloc_110 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_falloc_110 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_66 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.floc
d_floc_112 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_floc_112 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fpc
d_fpc_114 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 -> Integer
d_fpc_114 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps
d_FlatSteps_118 a0 a1 a2 a3 a4 = ()
data T_FlatSteps_118
  = C_'91''93'_124 |
    C__'8759'__134 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_FlatSteps_118
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  T_FlatSteps_118 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_146 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-step1
d_flat'45'step1_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_118
d_flat'45'step1_170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_flat'45'step1_170 v4 v5 v6
du_flat'45'step1_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_118
du_flat'45'step1_170 v0 v1 v2
  = coe
      C__'8759'__134 v0
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe C_'91''93'_124)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-label
d_flat'45'label_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_190 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-jmp
d_flat'45'jmp_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_204 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_218 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_238 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_258 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_278 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_298 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_322 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_394 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-shift
d_flm'45'shift_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_408 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_478 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-prefix
d_flm'45'prefix_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_492 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_586 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified
d_RunReified_610 a0 a1 a2 a3 = ()
data T_RunReified_610
  = C_reified_642 Integer Integer
                  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 T_FlatSteps_118
                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_630 :: T_RunReified_610 -> Integer
d_steps'45'len_630 v0
  = case coe v0 of
      C_reified_642 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_632 :: T_RunReified_610 -> Integer
d_rest'45'fuel_632 v0
  = case coe v0 of
      C_reified_642 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settle
d_settle_634 ::
  T_RunReified_610 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_settle_634 v0
  = case coe v0 of
      C_reified_642 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.chain
d_chain_636 :: T_RunReified_610 -> T_FlatSteps_118
d_chain_636 v0
  = case coe v0 of
      C_reified_642 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settled
d_settled_638 ::
  T_RunReified_610 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_638 v0
  = case coe v0 of
      C_reified_642 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_640 ::
  T_RunReified_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_640 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.reify-run
d_reify'45'run_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RunReified_610
d_reify'45'run_650 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             C_reified_642 (0 :: Integer) (0 :: Integer) v3 (coe C_'91''93'_124)
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_486
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v3)) in
              coe
                (if coe v6
                   then coe
                          C_reified_642 (0 :: Integer) v1 v3 (coe C_'91''93'_124)
                          (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   else (let v7
                               = coe
                                   MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_142 (coe v2)
                                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v3)) in
                         coe
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> let v9
                                         = d_reify'45'run_650
                                             (coe v0) (coe v5) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_174
                                                v0 v8 v2 v3)
                                             erased in
                                   coe
                                     (case coe v9 of
                                        C_reified_642 v10 v11 v12 v13 v14
                                          -> coe
                                               C_reified_642 (addInt (coe (1 :: Integer)) (coe v10))
                                               v11 v12
                                               (coe
                                                  C__'8759'__134 v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased)
                                                  v13)
                                               v14
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     C_reified_642 (0 :: Integer) v1 v3 (coe C_'91''93'_124)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  T_FlatSteps_118 -> T_FlatSteps_118 -> T_FlatSteps_118
d_FlatSteps'45''43''43'_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_FlatSteps'45''43''43'_750 v7 v8
du_FlatSteps'45''43''43'_750 ::
  T_FlatSteps_118 -> T_FlatSteps_118 -> T_FlatSteps_118
du_FlatSteps'45''43''43'_750 v0 v1
  = case coe v0 of
      C_'91''93'_124 -> coe v1
      C__'8759'__134 v5 v6 v7
        -> coe
             C__'8759'__134 v5 v6
             (coe du_FlatSteps'45''43''43'_750 (coe v7) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps
d_chain'45'steps_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56) ->
  (Integer -> T_FlatSteps_118) -> T_FlatSteps_118
d_chain'45'steps_770 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_chain'45'steps_770 v3 v5
du_chain'45'steps_770 ::
  Integer -> (Integer -> T_FlatSteps_118) -> T_FlatSteps_118
du_chain'45'steps_770 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_124
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_FlatSteps'45''43''43'_750 (coe v1 (0 :: Integer))
                (coe
                   du_chain'45'steps_770 (coe v2)
                   (coe (\ v3 -> coe v1 (addInt (coe (1 :: Integer)) (coe v3))))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56) ->
  (Integer -> T_FlatSteps_118) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_800 = erased
