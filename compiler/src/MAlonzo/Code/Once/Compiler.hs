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
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Verified
import qualified MAlonzo.Code.Once.Verified.ArchCorrectness
import qualified MAlonzo.Code.Once.Verified.CPU
import qualified MAlonzo.Code.Once.Verified.Compile
import qualified MAlonzo.Code.Once.Verified.SourceTrace

-- Once.Compiler.VC.codegen-asm-correct
d_codegen'45'asm'45'correct_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_6 = erased
-- Once.Compiler.VC.compile
d_compile_8 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_8
  = coe
      MAlonzo.Code.Once.Verified.Compile.du_compile_136
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correct
d_correct_10 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_10 = erased
-- Once.Compiler.VC.exec
d_exec_12 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_exec_12
  = coe
      MAlonzo.Code.Once.Verified.Compile.du_exec_126
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.module-to-asm-correct
d_module'45'to'45'asm'45'correct_14 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_14 = erased
-- Once.Compiler.VC.string-to-bytes
d_string'45'to'45'bytes_16 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_16
  = coe
      MAlonzo.Code.Once.Verified.Compile.du_string'45'to'45'bytes_132
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_18 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_18 = erased
-- Once.Compiler.VC.⟦_⟧A_
d_'10214'_'10215'A__20 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_'10214'_'10215'A__20
  = coe
      MAlonzo.Code.Once.Verified.Compile.du_'10214'_'10215'A__174
      (coe
         MAlonzo.Code.Once.Verified.ArchCorrectness.d_arch'45'correctness_12)
-- Once.Compiler.once-compiler
d_once'45'compiler_22 ::
  MAlonzo.Code.Once.Verified.T_CorrectCompiler_4
d_once'45'compiler_22
  = coe
      MAlonzo.Code.Once.Verified.C_constructor_54
      MAlonzo.Code.Once.Verified.SourceTrace.d_'10214'_'10215'_62
      (coe
         MAlonzo.Code.Once.Verified.Compile.du_exec_126
         (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6))
      (coe
         MAlonzo.Code.Once.Verified.Compile.du_compile_136
         (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6))
      erased
