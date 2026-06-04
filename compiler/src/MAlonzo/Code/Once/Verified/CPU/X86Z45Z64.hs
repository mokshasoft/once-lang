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

module MAlonzo.Code.Once.Verified.CPU.X86Z45Z64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.CPU.X86-64.observe-x86-64
d_observe'45'x86'45'64_8 ::
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Maybe Integer
d_observe'45'x86'45'64_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> let v2
                 = MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
                     (coe v1) in
           coe
             (if coe v2
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                             (coe v1))
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.X86-64.decode-x86-64
d_decode'45'x86'45'64_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-64.decode-x86-64"
-- Once.Verified.CPU.X86-64.assemble-x86-64
d_assemble'45'x86'45'64_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-64.assemble-x86-64"
-- Once.Verified.CPU.X86-64.arch-semantics
d_arch'45'semantics_24 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18
d_arch'45'semantics_24
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.C_constructor_62
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_initState_246
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_run_598
      d_observe'45'x86'45'64_8 d_decode'45'x86'45'64_20
      d_assemble'45'x86'45'64_22
