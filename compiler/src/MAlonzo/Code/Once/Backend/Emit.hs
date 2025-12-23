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

module MAlonzo.Code.Once.Backend.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Backend.AArch64.CodeGen
import qualified MAlonzo.Code.Once.Backend.AArch64.Emit
import qualified MAlonzo.Code.Once.Backend.RiscV64.CodeGen
import qualified MAlonzo.Code.Once.Backend.RiscV64.Emit
import qualified MAlonzo.Code.Once.Backend.X86.CodeGen
import qualified MAlonzo.Code.Once.Backend.X86.Emit
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.Emit.compileAArch64ToText
d_compileAArch64ToText_10 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAArch64ToText_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Backend.AArch64.Emit.d_programToText_104
      (coe
         MAlonzo.Code.Once.Backend.AArch64.CodeGen.d_compile'45'aarch64_32
         (coe v0) (coe v1) (coe v2))
-- Once.Backend.Emit.compileX86ToText
d_compileX86ToText_18 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileX86ToText_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Backend.X86.Emit.d_programToText_76
      (coe
         MAlonzo.Code.Once.Backend.X86.CodeGen.d_compile'45'x86_32 (coe v0)
         (coe v1) (coe v2))
-- Once.Backend.Emit.compileRiscVToText
d_compileRiscVToText_26 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileRiscVToText_26 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Backend.RiscV64.Emit.d_programToText_278
      (coe
         MAlonzo.Code.Once.Backend.RiscV64.CodeGen.d_compile'45'riscv_34
         (coe v0) (coe v1) (coe v2))
