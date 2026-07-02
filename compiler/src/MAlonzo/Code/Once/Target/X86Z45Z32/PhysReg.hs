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

module MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Target.X86-32.PhysReg.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_eax_10 | C_ebx_12 | C_ecx_14 | C_edx_16 | C_esi_18 | C_edi_20 |
    C_ebp_22 | C_esp_24
-- Once.Target.X86-32.PhysReg.showReg
d_showReg_26 ::
  T_Reg_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_26 v0
  = case coe v0 of
      C_eax_10 -> coe ("%eax" :: Data.Text.Text)
      C_ebx_12 -> coe ("%ebx" :: Data.Text.Text)
      C_ecx_14 -> coe ("%ecx" :: Data.Text.Text)
      C_edx_16 -> coe ("%edx" :: Data.Text.Text)
      C_esi_18 -> coe ("%esi" :: Data.Text.Text)
      C_edi_20 -> coe ("%edi" :: Data.Text.Text)
      C_ebp_22 -> coe ("%ebp" :: Data.Text.Text)
      C_esp_24 -> coe ("%esp" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.X86-32.PhysReg.RegClass
d_RegClass_28 = ()
data T_RegClass_28 = C_io_30 | C_ccc_32 | C_arith_34 | C_free_36
-- Once.Target.X86-32.PhysReg.owner
d_owner_38 :: T_Reg_8 -> T_RegClass_28
d_owner_38 v0
  = case coe v0 of
      C_eax_10 -> coe C_io_30
      C_ebx_12 -> coe C_ccc_32
      C_ecx_14 -> coe C_io_30
      C_edx_16 -> coe C_ccc_32
      C_esi_18 -> coe C_ccc_32
      C_edi_20 -> coe C_ccc_32
      C_ebp_22 -> coe C_ccc_32
      C_esp_24 -> coe C_ccc_32
      _ -> MAlonzo.RTE.mazUnreachableError
