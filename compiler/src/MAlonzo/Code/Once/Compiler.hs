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

module MAlonzo.Code.Once.Compiler where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Once.Adequacy
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Compiler.VC._≋_
d__'8779'__6 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d__'8779'__6 = erased
-- Once.Compiler.VC.TraceAt
d_TraceAt_8 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_8 = erased
-- Once.Compiler.VC.codegen-asm-correct
d_codegen'45'asm'45'correct_10 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_10 = erased
-- Once.Compiler.VC.compile
d_compile_12 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_12
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile_174
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-cr
d_compile'45'cr_14 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_14
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'cr_136
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-gm
d_compile'45'gm_16 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_16
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'gm_162
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-mir
d_compile'45'mir_18 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_18
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'mir_148
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correct
d_correct_20 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_20
  = coe MAlonzo.Code.Once.Adequacy.Compile.du_correct_426
-- Once.Compiler.VC.correct-cr
d_correct'45'cr_22 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_22 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'cr_296 v4 v5 v7
-- Once.Compiler.VC.correct-gm
d_correct'45'gm_24 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_24 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'gm_400 v0 v1 v2
-- Once.Compiler.VC.correct-mir
d_correct'45'mir_26 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_26 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'mir_366 v0 v1 v2
      v3
-- Once.Compiler.VC.exec
d_exec_28 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_exec_28
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_exec_126
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.module-to-asm-correct
d_module'45'to'45'asm'45'correct_30 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_30 = erased
-- Once.Compiler.VC.opt-trace
d_opt'45'trace_32 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opt'45'trace_32 = erased
-- Once.Compiler.VC.string-to-bytes
d_string'45'to'45'bytes_34 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_34
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_string'45'to'45'bytes_132
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_36 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_36 = erased
-- Once.Compiler.VC.⟦_⟧A_
d_'10214'_'10215'A__38 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'A__38
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215'A__182
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.d_arch'45'correctness_12)
-- Once.Compiler.VC.⟦_⟧⊥
d_'10214'_'10215''8869'_40 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869'_40
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869'_250
-- Once.Compiler.VC.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_42 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'ir_42
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'ir_242
-- Once.Compiler.VC.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_44 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'm_44
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'm_246
-- Once.Compiler.once-compiler
d_once'45'compiler_46 ::
  MAlonzo.Code.Once.Adequacy.T_CorrectCompiler_4
d_once'45'compiler_46
  = coe
      MAlonzo.Code.Once.Adequacy.C_constructor_54
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869'_250)
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_exec_126
         (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6))
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_compile_174
         (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6))
      (coe MAlonzo.Code.Once.Adequacy.Compile.du_correct_426)
