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
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_48 ~v0 = du_do'45'jump_48
du_do'45'jump_48 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_48
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_224
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.exec-flat
d_exec'45'flat_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_exec'45'flat_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_618 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fetch
d_fetch_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_86 ~v0 = du_fetch_86
du_fetch_86 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_86 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.find-label
d_find'45'label_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
d_find'45'label_94 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-go
d_fl'45'go_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_100 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_116 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.fl-label-match
d_fl'45'label'45'match_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_104 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_118
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-exec-instr
d_flat'45'exec'45'instr_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.flat-read-tag
d_flat'45'read'45'tag_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_110 ~v0 = du_flat'45'read'45'tag_110
du_flat'45'read'45'tag_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_110
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.label-of?
d_label'45'of'63'_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
d_label'45'of'63'_132 ~v0 = du_label'45'of'63'_132
du_label'45'of'63'_132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
du_label'45'of'63'_132
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_112
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.sv-is-zero
d_sv'45'is'45'zero_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_160 ~v0 = du_sv'45'is'45'zero_160
du_sv'45'is'45'zero_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_160
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.tag-zf
d_tag'45'zf_162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_162 ~v0 = du_tag'45'zf_162
du_tag'45'zf_162 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_162
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.falloc
d_falloc_170 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_170 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fclosure
d_fclosure_172 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_172 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.floc
d_floc_174 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_174 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fpc
d_fpc_176 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_176 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI._.FlatState.fret
d_fret_178 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_178 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps
d_FlatSteps_182 a0 a1 a2 a3 a4 = ()
data T_FlatSteps_182
  = C_'91''93'_188 |
    C__'8759'__198 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_FlatSteps_182
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatSteps_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_210 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-step1
d_flat'45'step1_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_182
d_flat'45'step1_234 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_flat'45'step1_234 v4 v5 v6
du_flat'45'step1_234 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatSteps_182
du_flat'45'step1_234 v0 v1 v2
  = coe
      C__'8759'__198 v0
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe C_'91''93'_188)
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-label
d_flat'45'label_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_254 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-jmp
d_flat'45'jmp_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_268 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_282 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_302 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_322 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_342 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_362 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_386 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_458 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-shift
d_flm'45'shift_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_472 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_542 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.flm-prefix
d_flm'45'prefix_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_556 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_650 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified
d_RunReified_674 a0 a1 a2 a3 = ()
data T_RunReified_674
  = C_reified_706 Integer Integer
                  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 T_FlatSteps_182
                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_694 :: T_RunReified_674 -> Integer
d_steps'45'len_694 v0
  = case coe v0 of
      C_reified_706 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_696 :: T_RunReified_674 -> Integer
d_rest'45'fuel_696 v0
  = case coe v0 of
      C_reified_706 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settle
d_settle_698 ::
  T_RunReified_674 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_settle_698 v0
  = case coe v0 of
      C_reified_706 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.chain
d_chain_700 :: T_RunReified_674 -> T_FlatSteps_182
d_chain_700 v0
  = case coe v0 of
      C_reified_706 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.settled
d_settled_702 ::
  T_RunReified_674 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_702 v0
  = case coe v0 of
      C_reified_706 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_704 ::
  T_RunReified_674 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_704 = erased
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.reify-run
d_reify'45'run_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RunReified_674
d_reify'45'run_714 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             C_reified_706 (0 :: Integer) (0 :: Integer) v3 (coe C_'91''93'_188)
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)) in
              coe
                (if coe v6
                   then coe
                          C_reified_706 (0 :: Integer) v1 v3 (coe C_'91''93'_188)
                          (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   else (let v7
                               = coe
                                   MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216 (coe v2)
                                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3)) in
                         coe
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> let v9
                                         = d_reify'45'run_714
                                             (coe v0) (coe v5) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
                                                v0 v8 v2 v3)
                                             erased in
                                   coe
                                     (case coe v9 of
                                        C_reified_706 v10 v11 v12 v13 v14
                                          -> coe
                                               C_reified_706 (addInt (coe (1 :: Integer)) (coe v10))
                                               v11 v12
                                               (coe
                                                  C__'8759'__198 v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased)
                                                  v13)
                                               v14
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     C_reified_706 (0 :: Integer) v1 v3 (coe C_'91''93'_188)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatSteps_182 -> T_FlatSteps_182 -> T_FlatSteps_182
d_FlatSteps'45''43''43'_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_FlatSteps'45''43''43'_814 v7 v8
du_FlatSteps'45''43''43'_814 ::
  T_FlatSteps_182 -> T_FlatSteps_182 -> T_FlatSteps_182
du_FlatSteps'45''43''43'_814 v0 v1
  = case coe v0 of
      C_'91''93'_188 -> coe v1
      C__'8759'__198 v5 v6 v7
        -> coe
             C__'8759'__198 v5 v6
             (coe du_FlatSteps'45''43''43'_814 (coe v7) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps
d_chain'45'steps_834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62) ->
  (Integer -> T_FlatSteps_182) -> T_FlatSteps_182
d_chain'45'steps_834 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_chain'45'steps_834 v3 v5
du_chain'45'steps_834 ::
  Integer -> (Integer -> T_FlatSteps_182) -> T_FlatSteps_182
du_chain'45'steps_834 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_188
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_FlatSteps'45''43''43'_814 (coe v1 (0 :: Integer))
                (coe
                   du_chain'45'steps_834 (coe v2)
                   (coe (\ v3 -> coe v1 (addInt (coe (1 :: Integer)) (coe v3))))))
-- Once.CCC.Codegen.FlatStepLemmas.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62) ->
  (Integer -> T_FlatSteps_182) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_864 = erased
