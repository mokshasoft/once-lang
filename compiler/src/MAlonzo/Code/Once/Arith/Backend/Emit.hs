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

module MAlonzo.Code.Once.Arith.Backend.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Arith.Backend.AArch64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax
import qualified MAlonzo.Code.Once.Arith.Backend.X86.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86.Syntax

-- Once.Arith.Backend.Emit.emitX86
d_emitX86_8 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitX86_8
  = coe MAlonzo.Code.Once.Arith.Backend.X86.Emit.d_emitProgram_150
-- Once.Arith.Backend.Emit.emitAArch64
d_emitAArch64_10 ::
  [MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_ArithInstr_224] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitAArch64_10
  = coe
      MAlonzo.Code.Once.Arith.Backend.AArch64.Emit.d_emitProgram_178
-- Once.Arith.Backend.Emit.emitRiscV
d_emitRiscV_12 ::
  [MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_ArithInstr_222] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitRiscV_12
  = coe MAlonzo.Code.Once.Arith.Backend.RiscV.Emit.d_emitProgram_190
