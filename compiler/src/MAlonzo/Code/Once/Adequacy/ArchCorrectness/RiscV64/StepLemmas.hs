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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.exec-1
d_exec'45'1_18 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'1_18 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-label
d_step'45'label_44 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'label_44 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-nop
d_step'45'nop_56 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'nop_56 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-mv
d_step'45'mv_72 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mv_72 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-li
d_step'45'li_88 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'li_88 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-addi
d_step'45'addi_106 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'addi_106 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-sltu
d_step'45'sltu_124 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sltu_124 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-add
d_step'45'add_142 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'add_142 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-sub
d_step'45'sub_160 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sub_160 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-ld
d_step'45'ld_180 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ld_180 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-sd
d_step'45'sd_204 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'sd_204 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-lla
d_step'45'lla_222 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lla_222 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-lla-sym
d_step'45'lla'45'sym_244 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lla'45'sym_244 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-lla-missing
d_step'45'lla'45'missing_260 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'lla'45'missing_260 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-j
d_step'45'j_280 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'j_280 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.execInstr-ld
d_execInstr'45'ld_300 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_execInstr'45'ld_300 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-jalr
d_step'45'jalr_330 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jalr_330 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-ret
d_step'45'ret_342 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'ret_342 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-call-sym
d_step'45'call'45'sym_356 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'call'45'sym_356 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-unimp
d_step'45'unimp_368 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'unimp_368 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-fetch-none
d_step'45'fetch'45'none_380 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'fetch'45'none_380 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-beq-taken
d_step'45'beq'45'taken_400 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'beq'45'taken_400 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-beq-not
d_step'45'beq'45'not_430 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'beq'45'not_430 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-j-found
d_step'45'j'45'found_452 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'j'45'found_452 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas.step-jal-found
d_step'45'jal'45'found_476 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'jal'45'found_476 = erased
