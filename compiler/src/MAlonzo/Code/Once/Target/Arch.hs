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

module MAlonzo.Code.Once.Target.Arch where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Float.Dyadic

-- Once.Target.Arch.Arch
d_Arch_6 = ()
data T_Arch_6 = C_x86'45'64_8 | C_x86'45'32_10 | C_riscv64_12
-- Once.Target.Arch.arch-float-format
d_arch'45'float'45'format_14 ::
  T_Arch_6 -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_arch'45'float'45'format_14 v0
  = case coe v0 of
      C_x86'45'64_8 -> coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42
      C_x86'45'32_10 -> coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40
      C_riscv64_12 -> coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42
      _ -> MAlonzo.RTE.mazUnreachableError
