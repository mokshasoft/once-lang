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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.StepLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.≡ᵇ-refl
d_'8801''7495''45'refl_12 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_12 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.self≢plus
d_self'8802'plus_20 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_self'8802'plus_20 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.+-cancelᵇ
d_'43''45'cancel'7495'_34 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'7495'_34 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.read-write-same
d_read'45'write'45'same_52 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'same_52 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.read-write-diff
d_read'45'write'45'diff_72 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'diff_72 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.exec-1
d_exec'45'1_96 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'1_96 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-label
d_step'45'label_122 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'label_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-rr
d_step'45'mov'45'rr_138 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rr_138 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-push
d_step'45'push_152 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'push_152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea
d_step'45'lea_170 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea-sym
d_step'45'lea'45'sym_186 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea'45'sym_186 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea-label
d_step'45'lea'45'label_204 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea'45'label_204 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-pop
d_step'45'pop_226 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'pop_226 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-ri
d_step'45'mov'45'ri_248 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'ri_248 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-rm
d_step'45'mov'45'rm_266 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rm_266 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-mi
d_step'45'mov'45'mi_288 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mi_288 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-mr
d_step'45'mov'45'mr_304 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mr_304 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-cmp-ri
d_step'45'cmp'45'ri_320 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'ri_320 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-cmp-mi
d_step'45'cmp'45'mi_338 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'mi_338 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-call
d_step'45'call_360 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call_360 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-call-l
d_step'45'call'45'l_382 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'l_382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-ret
d_step'45'ret_402 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ret_402 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-add-ri
d_step'45'add'45'ri_424 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'ri_424 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-add-rr
d_step'45'add'45'rr_440 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'rr_440 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-sub-ri
d_step'45'sub'45'ri_456 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sub'45'ri_456 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jmp
d_step'45'jmp_472 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp_472 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-je-taken
d_step'45'je'45'taken_494 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'taken_494 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-je-not
d_step'45'je'45'not_520 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'not_520 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jne-taken
d_step'45'jne'45'taken_542 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'taken_542 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jne-not
d_step'45'jne'45'not_568 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'not_568 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.Steps
d_Steps_584 a0 a1 a2 a3 = ()
data T_Steps_584
  = C_'91''93'_590 |
    C__'8759'__600 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Steps_584
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.exec-steps
d_exec'45'steps_612 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  T_Steps_584 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'steps_612 = erased
