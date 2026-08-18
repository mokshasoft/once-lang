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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.Role
d_Role_10 = ()
data T_Role_10
  = C_role'45'sp_12 | C_role'45'clos_14 | C_role'45'heap_16 |
    C_role'45'out_18 | C_role'45'in1_20 | C_role'45'scratch_22 |
    C_role'45'count_24
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles
d_RegRoles_28 a0 = ()
newtype T_RegRoles_28 = C_constructor_50 (T_Role_10 -> AgdaAny)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.reg-of
d_reg'45'of_34 :: T_RegRoles_28 -> T_Role_10 -> AgdaAny
d_reg'45'of_34 v0
  = case coe v0 of
      C_constructor_50 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.sp-reg
d_sp'45'reg_36 :: () -> T_RegRoles_28 -> AgdaAny
d_sp'45'reg_36 ~v0 v1 = du_sp'45'reg_36 v1
du_sp'45'reg_36 :: T_RegRoles_28 -> AgdaAny
du_sp'45'reg_36 v0 = coe d_reg'45'of_34 v0 (coe C_role'45'sp_12)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.clos-reg
d_clos'45'reg_38 :: () -> T_RegRoles_28 -> AgdaAny
d_clos'45'reg_38 ~v0 v1 = du_clos'45'reg_38 v1
du_clos'45'reg_38 :: T_RegRoles_28 -> AgdaAny
du_clos'45'reg_38 v0
  = coe d_reg'45'of_34 v0 (coe C_role'45'clos_14)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.heap-reg
d_heap'45'reg_40 :: () -> T_RegRoles_28 -> AgdaAny
d_heap'45'reg_40 ~v0 v1 = du_heap'45'reg_40 v1
du_heap'45'reg_40 :: T_RegRoles_28 -> AgdaAny
du_heap'45'reg_40 v0
  = coe d_reg'45'of_34 v0 (coe C_role'45'heap_16)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.out-reg
d_out'45'reg_42 :: () -> T_RegRoles_28 -> AgdaAny
d_out'45'reg_42 ~v0 v1 = du_out'45'reg_42 v1
du_out'45'reg_42 :: T_RegRoles_28 -> AgdaAny
du_out'45'reg_42 v0 = coe d_reg'45'of_34 v0 (coe C_role'45'out_18)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.in1-reg
d_in1'45'reg_44 :: () -> T_RegRoles_28 -> AgdaAny
d_in1'45'reg_44 ~v0 v1 = du_in1'45'reg_44 v1
du_in1'45'reg_44 :: T_RegRoles_28 -> AgdaAny
du_in1'45'reg_44 v0 = coe d_reg'45'of_34 v0 (coe C_role'45'in1_20)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.scratch-reg
d_scratch'45'reg_46 :: () -> T_RegRoles_28 -> AgdaAny
d_scratch'45'reg_46 ~v0 v1 = du_scratch'45'reg_46 v1
du_scratch'45'reg_46 :: T_RegRoles_28 -> AgdaAny
du_scratch'45'reg_46 v0
  = coe d_reg'45'of_34 v0 (coe C_role'45'scratch_22)
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.RegRoles.count-reg
d_count'45'reg_48 :: () -> T_RegRoles_28 -> AgdaAny
d_count'45'reg_48 ~v0 v1 = du_count'45'reg_48 v1
du_count'45'reg_48 :: T_RegRoles_28 -> AgdaAny
du_count'45'reg_48 v0
  = coe d_reg'45'of_34 v0 (coe C_role'45'count_24)
