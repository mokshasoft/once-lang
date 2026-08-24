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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word

-- Once.Target.Arch.Arch
d_Arch_6 = ()
data T_Arch_6 = C_x86'45'64_8 | C_x86'45'32_10 | C_riscv64_12
-- Once.Target.Arch.TargetNum
d_TargetNum_14 = ()
data T_TargetNum_14
  = C_mkTargetNum_28 Integer
                     MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Target.Arch.TargetNum.int-bits
d_int'45'bits_22 :: T_TargetNum_14 -> Integer
d_int'45'bits_22 v0
  = case coe v0 of
      C_mkTargetNum_28 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.TargetNum.float-format
d_float'45'format_24 ::
  T_TargetNum_14 -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_24 v0
  = case coe v0 of
      C_mkTargetNum_28 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.TargetNum.int-bits-pos
d_int'45'bits'45'pos_26 ::
  T_TargetNum_14 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_int'45'bits'45'pos_26 v0
  = case coe v0 of
      C_mkTargetNum_28 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.pos⇒suc
d_pos'8658'suc_34 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pos'8658'suc_34 v0 ~v1 = du_pos'8658'suc_34 v0
du_pos'8658'suc_34 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pos'8658'suc_34 v0
  = let v1 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
-- Once.Target.Arch.tn-lower
d_tn'45'lower_42 ::
  T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_tn'45'lower_42 v0 v1 ~v2 = du_tn'45'lower_42 v0 v1
du_tn'45'lower_42 :: T_TargetNum_14 -> Integer -> Integer
du_tn'45'lower_42 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_toWord_68 (coe d_int'45'bits_22 (coe v0))
      (coe v1)
-- Once.Target.Arch.tn-exact
d_tn'45'exact_56 ::
  T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tn'45'exact_56 = erased
-- Once.Target.Arch.arch-numerics
d_arch'45'numerics_78 :: T_Arch_6 -> T_TargetNum_14
d_arch'45'numerics_78 v0
  = case coe v0 of
      C_x86'45'64_8
        -> coe
             C_mkTargetNum_28 (coe (64 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      C_x86'45'32_10
        -> coe
             C_mkTargetNum_28 (coe (32 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      C_riscv64_12
        -> coe
             C_mkTargetNum_28 (coe (64 :: Integer))
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Arch.arch-int-bits
d_arch'45'int'45'bits_80 :: T_Arch_6 -> Integer
d_arch'45'int'45'bits_80 v0
  = coe d_int'45'bits_22 (coe d_arch'45'numerics_78 (coe v0))
-- Once.Target.Arch.arch-float-format
d_arch'45'float'45'format_84 ::
  T_Arch_6 -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_arch'45'float'45'format_84 v0
  = coe d_float'45'format_24 (coe d_arch'45'numerics_78 (coe v0))
-- Once.Target.Arch.archName
d_archName_88 ::
  T_Arch_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_archName_88 v0
  = case coe v0 of
      C_x86'45'64_8 -> coe ("x86-64" :: Data.Text.Text)
      C_x86'45'32_10 -> coe ("x86-32" :: Data.Text.Text)
      C_riscv64_12 -> coe ("riscv64" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
