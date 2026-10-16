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

-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.self≢plus
d_self'8802'plus_14 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_self'8802'plus_14 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.+-cancelᵇ
d_'43''45'cancel'7495'_28 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'7495'_28 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.read-write-same
d_read'45'write'45'same_46 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'same_46 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.read-write-diff
d_read'45'write'45'diff_66 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'diff_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.exec-1
d_exec'45'1_90 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'1_90 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-label
d_step'45'label_116 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'label_116 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-nop
d_step'45'nop_128 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'nop_128 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-rr
d_step'45'mov'45'rr_144 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rr_144 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-ri
d_step'45'mov'45'ri_160 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'ri_160 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-rm
d_step'45'mov'45'rm_178 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'rm_178 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-mi
d_step'45'mov'45'mi_200 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mi_200 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-mr
d_step'45'mov'45'mr_216 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'mr_216 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-code
d_step'45'mov'45'code_234 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'code_234 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-mov-code-miss
d_step'45'mov'45'code'45'miss_256 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mov'45'code'45'miss_256 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-lea
d_step'45'lea_278 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lea_278 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-push
d_step'45'push_292 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'push_292 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-pop
d_step'45'pop_308 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'pop_308 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-add-ri
d_step'45'add'45'ri_330 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'ri_330 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-sbb-rr
d_step'45'sbb'45'rr_346 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sbb'45'rr_346 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.nz-val
d_nz'45'val_356 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'45'val_356 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas._.n1
d_n1_366 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n1_366 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas._.go
d_go_370 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_370 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-add-rr
d_step'45'add'45'rr_388 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add'45'rr_388 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-sub-ri
d_step'45'sub'45'ri_404 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sub'45'ri_404 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-cmp-ri
d_step'45'cmp'45'ri_420 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'ri_420 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-cmp-mi
d_step'45'cmp'45'mi_438 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp'45'mi_438 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call
d_step'45'call_460 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call_460 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call-sym
d_step'45'call'45'sym_480 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'sym_480 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-call-l
d_step'45'call'45'l_496 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'l_496 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-ret
d_step'45'ret_516 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ret_516 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-l
d_step'45'jmp'45'l_538 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'l_538 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-l-miss
d_step'45'jmp'45'l'45'miss_558 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'l'45'miss_558 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jmp-i
d_step'45'jmp'45'i_578 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jmp'45'i_578 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-taken
d_step'45'je'45'taken_594 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'taken_594 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-miss
d_step'45'je'45'miss_620 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'miss_620 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-je-not
d_step'45'je'45'not_646 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je'45'not_646 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jne-taken
d_step'45'jne'45'taken_668 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'taken_668 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-jne-not
d_step'45'jne'45'not_694 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jne'45'not_694 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.step-ud2
d_step'45'ud2_712 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ud2_712 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.Steps
d_Steps_722 a0 a1 a2 a3 = ()
data T_Steps_722
  = C_'91''93'_728 |
    C__'8759'__738 MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304
                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Steps_722
-- Once.Adequacy.ArchCorrectness.X86-32.StepLemmas.exec-steps
d_exec'45'steps_750 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_304 ->
  T_Steps_722 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'steps_750 = erased
