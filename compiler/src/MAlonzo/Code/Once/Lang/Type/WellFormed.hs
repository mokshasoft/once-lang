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

module MAlonzo.Code.Once.Lang.Type.WellFormed where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Type.WellFormed.IsBaseType
d_IsBaseType_8 a0 = ()
data T_IsBaseType_8
  = C_base'45'Unit_10 | C_base'45'Void_12 | C_base'45'Int_14 |
    C_base'45'Float_16 |
    C_base'45'Prod_22 T_IsBaseType_8 T_IsBaseType_8 |
    C_base'45'Sum_28 T_IsBaseType_8 T_IsBaseType_8 | C_base'45'rigid_32
-- Once.Lang.Type.WellFormed.IsConcrete
d_IsConcrete_34 a0 = ()
data T_IsConcrete_34
  = C_con'45'base_38 T_IsBaseType_8 |
    C_con'45'fun_46 T_IsBaseType_8 T_IsBaseType_8
-- Once.Lang.Type.WellFormed.WellFormedF
d_WellFormedF_48 a0 = ()
data T_WellFormedF_48
  = C_wf'45'K_52 T_IsBaseType_8 | C_wf'45'Id_54 |
    C_wf'45'Sum_60 T_WellFormedF_48 T_WellFormedF_48 |
    C_wf'45'Prod_66 T_WellFormedF_48 T_WellFormedF_48
-- Once.Lang.Type.WellFormed.RigidFree
d_RigidFree_68 a0 = ()
data T_RigidFree_68
  = C_rf'45'Unit_72 | C_rf'45'Void_74 | C_rf'45'Int_76 |
    C_rf'45'Float_78 | C_rf'45''42'_84 T_RigidFree_68 T_RigidFree_68 |
    C_rf'45''43'_90 T_RigidFree_68 T_RigidFree_68 |
    C_rf'45''8658'_98 T_RigidFree_68 T_RigidFree_68 |
    C_rf'45'μ_102 T_RigidFreeF_70 | C_rf'45'ν_108 T_RigidFreeF_70
-- Once.Lang.Type.WellFormed.RigidFreeF
d_RigidFreeF_70 a0 = ()
data T_RigidFreeF_70
  = C_rf'45'K_112 T_RigidFree_68 | C_rf'45'Id_114 |
    C_rf'45''8853'_120 T_RigidFreeF_70 T_RigidFreeF_70 |
    C_rf'45''8855'_126 T_RigidFreeF_70 T_RigidFreeF_70
