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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Float.Dyadic

-- Once.Target.Arch.Arch
d_Arch_6 = ()
data T_Arch_6 = C_x86'45'64_8 | C_x86'45'32_10 | C_riscv64_12
-- Once.Target.Arch.TargetNum
d_TargetNum_14 = ()
data T_TargetNum_14
  = C_mkTargetNum_24 Integer
                     MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
-- Once.Target.Arch.TargetNum.int-bits
d_int'45'bits_20 :: T_TargetNum_14 -> Integer
d_int'45'bits_20 v0
  = case coe v0 of
      C_mkTargetNum_24 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.TargetNum.float-format
d_float'45'format_22 ::
  T_TargetNum_14 -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_22 v0
  = case coe v0 of
      C_mkTargetNum_24 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.arch-numerics
d_arch'45'numerics_26 :: T_Arch_6 -> T_TargetNum_14
d_arch'45'numerics_26 v0
  = case coe v0 of
      C_x86'45'64_8
        -> coe
             C_mkTargetNum_24 (coe (64 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
      C_x86'45'32_10
        -> coe
             C_mkTargetNum_24 (coe (32 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
      C_riscv64_12
        -> coe
             C_mkTargetNum_24 (coe (64 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.arch-int-bits
d_arch'45'int'45'bits_28 :: T_Arch_6 -> Integer
d_arch'45'int'45'bits_28 v0
  = coe d_int'45'bits_20 (coe d_arch'45'numerics_26 (coe v0))
-- Once.Target.Arch.arch-float-format
d_arch'45'float'45'format_32 ::
  T_Arch_6 -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_arch'45'float'45'format_32 v0
  = coe d_float'45'format_22 (coe d_arch'45'numerics_26 (coe v0))
-- Once.Target.Arch.archName
d_archName_36 ::
  T_Arch_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_archName_36 v0
  = case coe v0 of
      C_x86'45'64_8 -> coe ("x86-64" :: Data.Text.Text)
      C_x86'45'32_10 -> coe ("x86-32" :: Data.Text.Text)
      C_riscv64_12 -> coe ("riscv64" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
