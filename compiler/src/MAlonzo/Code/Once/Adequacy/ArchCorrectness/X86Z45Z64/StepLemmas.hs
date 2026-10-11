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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.self≢plus
d_self'8802'plus_14 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_self'8802'plus_14 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.+-cancelᵇ
d_'43''45'cancel'7495'_28 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'7495'_28 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.read-write-same
d_read'45'write'45'same_46 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'same_46 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.read-write-diff
d_read'45'write'45'diff_66 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'diff_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.exec-1
d_exec'45'1_90 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'1_90 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-label
d_step'45'label_116 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'label_116 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-rr
d_step'45'mov'45'rr_132 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rr_132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-push
d_step'45'push_146 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'push_146 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea
d_step'45'lea_164 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea_164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea-sym
d_step'45'lea'45'sym_180 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea'45'sym_180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-lea-label
d_step'45'lea'45'label_198 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea'45'label_198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-pop
d_step'45'pop_220 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'pop_220 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-ri
d_step'45'mov'45'ri_242 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'ri_242 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-rm
d_step'45'mov'45'rm_260 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rm_260 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-mi
d_step'45'mov'45'mi_282 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mi_282 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-mov-mr
d_step'45'mov'45'mr_298 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mr_298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-cmp-ri
d_step'45'cmp'45'ri_314 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'ri_314 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-cmp-mi
d_step'45'cmp'45'mi_332 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'mi_332 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-call
d_step'45'call_354 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call_354 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-call-l
d_step'45'call'45'l_376 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'l_376 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-ret
d_step'45'ret_396 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ret_396 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-add-ri
d_step'45'add'45'ri_418 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'ri_418 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-sbb-rr
d_step'45'sbb'45'rr_434 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sbb'45'rr_434 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.nz-val
d_nz'45'val_444 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'45'val_444 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas._.n1
d_n1_454 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n1_454 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas._.go
d_go_458 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_458 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-add-rr
d_step'45'add'45'rr_476 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'rr_476 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-sub-ri
d_step'45'sub'45'ri_492 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sub'45'ri_492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jmp
d_step'45'jmp_508 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp_508 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-je-taken
d_step'45'je'45'taken_530 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'taken_530 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-je-not
d_step'45'je'45'not_556 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'not_556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jne-taken
d_step'45'jne'45'taken_578 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'taken_578 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.step-jne-not
d_step'45'jne'45'not_604 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'not_604 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.Steps
d_Steps_620 a0 a1 a2 a3 = ()
data T_Steps_620
  = C_'91''93'_626 |
    C__'8759'__636 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Steps_620
-- Once.Adequacy.ArchCorrectness.X86-64.StepLemmas.exec-steps
d_exec'45'steps_648 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  T_Steps_620 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'steps_648 = erased
