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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.Arith.Backend.X86-32.Dispatch._.dispatch-arith
d_dispatch'45'arith_16 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_134 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_134
d_dispatch'45'arith_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.C_mkstate_156
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_146
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec'45'arith'45'block_88
            (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_148
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec'45'arith'45'block_88
            (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_flags_150
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec'45'arith'45'block_88
            (coe v0) (coe v1) (coe v2)))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_152
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_154
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec'45'arith'45'block_88
            (coe v0) (coe v1) (coe v2)))
