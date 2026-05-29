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

module MAlonzo.Code.Once.Verified.CPU.X86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.CPU.X86-32.observe-x86-32
d_observe'45'x86'45'32_8 ::
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_134 ->
  Maybe Integer
d_observe'45'x86'45'32_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> let v2
                 = MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_154
                     (coe v1) in
           coe
             (if coe v2
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_48
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_146
                             (coe v1))
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebx_14))
                else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.X86-32.decode-x86-32
d_decode'45'x86'45'32_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-32.decode-x86-32"
-- Once.Verified.CPU.X86-32.assemble-x86-32
d_assemble'45'x86'45'32_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-32.assemble-x86-32"
-- Once.Verified.CPU.X86-32.arch-semantics
d_arch'45'semantics_24 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18
d_arch'45'semantics_24
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.C_constructor_62
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initState_166
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_run_504
      d_observe'45'x86'45'32_8 d_decode'45'x86'45'32_20
      d_assemble'45'x86'45'32_22
