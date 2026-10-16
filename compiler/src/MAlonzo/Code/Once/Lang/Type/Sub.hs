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

module MAlonzo.Code.Once.Lang.Type.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Type.Sub._⊑π_
d__'8849'π__8 a0 a1 = ()
data T__'8849'π__8
  = C_'8849''45'pure_10 | C_'8849''45'eff_12 | C_'8849''45'pe_14 |
    C_'8849''45'act_16 | C_'8849''45'pa_18 | C_'8849''45'ae_20 |
    C_'8849''45'g_22 | C_'8849''45'ge_24
-- Once.Lang.Type.Sub.·p-diag
d_'183'p'45'diag_28 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> T__'8849'π__8
d_'183'p'45'diag_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe C_'8849''45'pure_10
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe C_'8849''45'act_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe C_'8849''45'g_22
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe C_'8849''45'eff_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._<:_
d__'60''58'__30 a0 a1 = ()
data T__'60''58'__30
  = C_sub'45'void_34 | C_sub'45'unit_36 | C_sub'45'int_38 |
    C_sub'45'float_40 |
    C_sub'45'arr_56 T__'60''58'__30 T__'60''58'__30 T__'8849'π__8 |
    C_sub'45'prod_66 T__'60''58'__30 T__'60''58'__30 |
    C_sub'45'sum_76 T__'60''58'__30 T__'60''58'__30 | C_sub'45'μ_80 |
    C_sub'45'ν_88 T__'8849'π__8 | C_sub'45'rigid_94
-- Once.Lang.Type.Sub.⊑π-refl
d_'8849'π'45'refl_98 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> T__'8849'π__8
d_'8849'π'45'refl_98 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe C_'8849''45'pure_10
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe C_'8849''45'act_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe C_'8849''45'g_22
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe C_'8849''45'eff_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub.<:-refl
d_'60''58''45'refl_102 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'60''58'__30
d_'60''58''45'refl_102 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe C_sub'45'unit_36
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe C_sub'45'void_34
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             C_sub'45'prod_66 (d_'60''58''45'refl_102 (coe v1))
             (d_'60''58''45'refl_102 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             C_sub'45'sum_76 (d_'60''58''45'refl_102 (coe v1))
             (d_'60''58''45'refl_102 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v4 v5
               -> coe
                    C_sub'45'arr_56 (d_'60''58''45'refl_102 (coe v1))
                    (d_'60''58''45'refl_102 (coe v3)) (d_'8849'π'45'refl_98 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1 -> coe C_sub'45'μ_80
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe C_sub'45'ν_88 (d_'8849'π'45'refl_98 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe C_sub'45'int_38
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe C_sub'45'float_40
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe C_sub'45'rigid_94
      _ -> MAlonzo.RTE.mazUnreachableError
