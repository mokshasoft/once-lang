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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.StepLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.≡ᵇ-refl
d_'8801''7495''45'refl_12 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_12 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.self≢plus
d_self'8802'plus_20 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_self'8802'plus_20 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.+-cancelᵇ
d_'43''45'cancel'7495'_34 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'7495'_34 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.read-write-same
d_read'45'write'45'same_52 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'same_52 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.read-write-diff
d_read'45'write'45'diff_72 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'diff_72 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.exec-1
d_exec'45'1_96 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'1_96 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-label
d_step'45'label_122 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'label_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-nop
d_step'45'nop_134 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'nop_134 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-rr
d_step'45'mov'45'rr_150 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rr_150 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-ri
d_step'45'mov'45'ri_166 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'ri_166 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-rm
d_step'45'mov'45'rm_184 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rm_184 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-mi
d_step'45'mov'45'mi_206 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mi_206 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-mr
d_step'45'mov'45'mr_222 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mr_222 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-code
d_step'45'mov'45'code_240 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'code_240 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-code-miss
d_step'45'mov'45'code'45'miss_262 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'code'45'miss_262 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-lea
d_step'45'lea_284 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea_284 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-push
d_step'45'push_298 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'push_298 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-pop
d_step'45'pop_314 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'pop_314 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-add-ri
d_step'45'add'45'ri_336 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'ri_336 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-sbb-rr
d_step'45'sbb'45'rr_352 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sbb'45'rr_352 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.nz-val
d_nz'45'val_362 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'45'val_362 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas._.n1
d_n1_372 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n1_372 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas._.go
d_go_376 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_376 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-add-rr
d_step'45'add'45'rr_394 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'rr_394 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-sub-ri
d_step'45'sub'45'ri_410 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sub'45'ri_410 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-cmp-ri
d_step'45'cmp'45'ri_426 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'ri_426 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-cmp-mi
d_step'45'cmp'45'mi_444 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'mi_444 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call
d_step'45'call_466 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call_466 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call-sym
d_step'45'call'45'sym_486 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'sym_486 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call-l
d_step'45'call'45'l_502 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'l_502 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-ret
d_step'45'ret_522 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ret_522 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-l
d_step'45'jmp'45'l_544 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'l_544 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-l-miss
d_step'45'jmp'45'l'45'miss_564 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'l'45'miss_564 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-i
d_step'45'jmp'45'i_584 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'i_584 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-taken
d_step'45'je'45'taken_600 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'taken_600 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-miss
d_step'45'je'45'miss_626 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'miss_626 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-not
d_step'45'je'45'not_652 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'not_652 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jne-taken
d_step'45'jne'45'taken_674 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'taken_674 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jne-not
d_step'45'jne'45'not_700 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'not_700 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-ud2
d_step'45'ud2_718 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ud2_718 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.Steps
d_Steps_728 a0 a1 a2 a3 = ()
data T_Steps_728
  = C_'91''93'_734 |
    C__'8759'__744 MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Steps_728
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.exec-steps
d_exec'45'steps_756 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  T_Steps_728 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'steps_756 = erased
