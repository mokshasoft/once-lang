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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.arch-correctness
d_arch'45'correctness_22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_arch'45'correctness_22 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.d_x86'45'64'45'correct_428
             (coe v0)
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.d_x86'45'32'45'correct_150
             (coe v0)
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.d_riscv64'45'correct_150
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
