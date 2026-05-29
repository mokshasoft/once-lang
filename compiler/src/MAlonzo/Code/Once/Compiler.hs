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
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Verified
import qualified MAlonzo.Code.Once.Verified.Behavior
import qualified MAlonzo.Code.Once.Verified.CPU
import qualified MAlonzo.Code.Once.Verified.CPU.Interface
import qualified MAlonzo.Code.Once.Verified.Compile

-- Once.Compiler.VC.compile
d_compile_6 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_6
  = coe
      MAlonzo.Code.Once.Verified.Compile.d_compile_74
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correct
d_correct_8 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_8 = erased
-- Once.Compiler.VC.exec
d_exec_10 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe Integer
d_exec_10
  = coe
      MAlonzo.Code.Once.Verified.Compile.d_exec_64
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes
d_string'45'to'45'bytes_12 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_12
  = coe
      MAlonzo.Code.Once.Verified.Compile.d_string'45'to'45'bytes_70
      (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_14 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_14 = erased
-- Once.Compiler.once-compiler
d_once'45'compiler_16 ::
  MAlonzo.Code.Once.Verified.T_CorrectCompiler_4
d_once'45'compiler_16
  = coe
      MAlonzo.Code.Once.Verified.C_constructor_50
      MAlonzo.Code.Once.Verified.Behavior.d_'10214'_'10215'_10
      (MAlonzo.Code.Once.Verified.Compile.d_exec_64
         (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6))
      (MAlonzo.Code.Once.Verified.Compile.d_compile_74
         (coe MAlonzo.Code.Once.Verified.CPU.d_arch'45'semantics_6))
