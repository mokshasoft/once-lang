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

module MAlonzo.Code.Once.Internal.Type.WellFormed where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Type.WellFormed.IsBaseType
d_IsBaseType_8 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_IsBaseType_8 = erased
-- Once.Internal.Type.WellFormed.IsConcrete
d_IsConcrete_30 a0 = ()
data T_IsConcrete_30
  = C_con'45'base_34 MAlonzo.Code.Once.Spec.Type.T_Base_84 |
    C_con'45'fun_42 MAlonzo.Code.Once.Spec.Type.T_Base_84
                    MAlonzo.Code.Once.Spec.Type.T_Base_84
-- Once.Internal.Type.WellFormed.WellFormedF
d_WellFormedF_44 :: MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_WellFormedF_44 = erased
-- Once.Internal.Type.WellFormed.RigidFree
d_RigidFree_58 a0 = ()
data T_RigidFree_58
  = C_rf'45'Unit_62 | C_rf'45'Void_64 | C_rf'45'Int_66 |
    C_rf'45'Float_68 | C_rf'45''42'_74 T_RigidFree_58 T_RigidFree_58 |
    C_rf'45''43'_80 T_RigidFree_58 T_RigidFree_58 |
    C_rf'45''8658'_88 T_RigidFree_58 T_RigidFree_58 |
    C_rf'45'μ_92 T_RigidFreeF_60 | C_rf'45'ν_98 T_RigidFreeF_60
-- Once.Internal.Type.WellFormed.RigidFreeF
d_RigidFreeF_60 a0 = ()
data T_RigidFreeF_60
  = C_rf'45'K_102 T_RigidFree_58 | C_rf'45'Id_104 |
    C_rf'45''8853'_110 T_RigidFreeF_60 T_RigidFreeF_60 |
    C_rf'45''8855'_116 T_RigidFreeF_60 T_RigidFreeF_60
