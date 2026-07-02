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

module MAlonzo.Code.Once.Target.RiscV64.PhysReg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Target.RiscV64.PhysReg.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_zero_10 | C_ra_12 | C_sp_14 | C_fp_16 | C_a0_18 | C_a1_20 |
    C_a2_22 | C_a3_24 | C_a4_26 | C_a5_28 | C_a6_30 | C_a7_32 |
    C_s1_34 | C_s2_36 | C_s3_38 | C_s4_40 | C_t0_42 | C_t1_44 |
    C_t2_46 | C_t3_48 | C_t4_50
-- Once.Target.RiscV64.PhysReg.showReg
d_showReg_52 ::
  T_Reg_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_52 v0
  = case coe v0 of
      C_zero_10 -> coe ("zero" :: Data.Text.Text)
      C_ra_12 -> coe ("ra" :: Data.Text.Text)
      C_sp_14 -> coe ("sp" :: Data.Text.Text)
      C_fp_16 -> coe ("fp" :: Data.Text.Text)
      C_a0_18 -> coe ("a0" :: Data.Text.Text)
      C_a1_20 -> coe ("a1" :: Data.Text.Text)
      C_a2_22 -> coe ("a2" :: Data.Text.Text)
      C_a3_24 -> coe ("a3" :: Data.Text.Text)
      C_a4_26 -> coe ("a4" :: Data.Text.Text)
      C_a5_28 -> coe ("a5" :: Data.Text.Text)
      C_a6_30 -> coe ("a6" :: Data.Text.Text)
      C_a7_32 -> coe ("a7" :: Data.Text.Text)
      C_s1_34 -> coe ("s1" :: Data.Text.Text)
      C_s2_36 -> coe ("s2" :: Data.Text.Text)
      C_s3_38 -> coe ("s3" :: Data.Text.Text)
      C_s4_40 -> coe ("s4" :: Data.Text.Text)
      C_t0_42 -> coe ("t0" :: Data.Text.Text)
      C_t1_44 -> coe ("t1" :: Data.Text.Text)
      C_t2_46 -> coe ("t2" :: Data.Text.Text)
      C_t3_48 -> coe ("t3" :: Data.Text.Text)
      C_t4_50 -> coe ("t4" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.RiscV64.PhysReg.RegClass
d_RegClass_54 = ()
data T_RegClass_54 = C_io_56 | C_ccc_58 | C_arith_60 | C_free_62
-- Once.Target.RiscV64.PhysReg.owner
d_owner_64 :: T_Reg_8 -> T_RegClass_54
d_owner_64 v0
  = case coe v0 of
      C_zero_10 -> coe C_ccc_58
      C_ra_12 -> coe C_ccc_58
      C_sp_14 -> coe C_ccc_58
      C_fp_16 -> coe C_ccc_58
      C_a0_18 -> coe C_io_56
      C_a1_20 -> coe C_ccc_58
      C_a2_22 -> coe C_ccc_58
      C_a3_24 -> coe C_arith_60
      C_a4_26 -> coe C_arith_60
      C_a5_28 -> coe C_arith_60
      C_a6_30 -> coe C_ccc_58
      C_a7_32 -> coe C_ccc_58
      C_s1_34 -> coe C_ccc_58
      C_s2_36 -> coe C_ccc_58
      C_s3_38 -> coe C_ccc_58
      C_s4_40 -> coe C_ccc_58
      C_t0_42 -> coe C_io_56
      C_t1_44 -> coe C_ccc_58
      C_t2_46 -> coe C_ccc_58
      C_t3_48 -> coe C_ccc_58
      C_t4_50 -> coe C_ccc_58
      _ -> MAlonzo.RTE.mazUnreachableError
