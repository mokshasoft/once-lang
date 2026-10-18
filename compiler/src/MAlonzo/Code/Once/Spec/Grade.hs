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

module MAlonzo.Code.Once.Spec.Grade where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Spec.Grade.Quantity
d_Quantity_6 = ()
data T_Quantity_6 = C_Zero_8 | C_One_10 | C_Many_12
-- Once.Spec.Grade._+q_
d__'43'q__14 :: T_Quantity_6 -> T_Quantity_6 -> T_Quantity_6
d__'43'q__14 v0 v1
  = case coe v0 of
      C_Zero_8 -> coe v1
      C_One_10
        -> case coe v1 of
             C_Zero_8 -> coe v0
             C_One_10 -> coe C_Many_12
             C_Many_12 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_12 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Grade._*q_
d__'42'q__18 :: T_Quantity_6 -> T_Quantity_6 -> T_Quantity_6
d__'42'q__18 v0 v1
  = case coe v0 of
      C_Zero_8 -> coe v0
      C_One_10 -> coe v1
      C_Many_12
        -> case coe v1 of
             C_Zero_8 -> coe v1
             C_One_10 -> coe v0
             C_Many_12 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Grade._≤q_
d__'8804'q__22 a0 a1 = ()
data T__'8804'q__22
  = C_0'8804'q_26 | C_1'8804'1_28 | C_1'8804'ω_30 | C_ω'8804'ω_32
-- Once.Spec.Grade.Finite
d_Finite_34 = ()
data T_Finite_34 = C_pure'7584'_36 | C_act'7584'_38
-- Once.Spec.Grade.Purity
d_Purity_40 = ()
data T_Purity_40 = C_fin_42 T_Finite_34 | C_eff_44
-- Once.Spec.Grade._⊑π_
d__'8849'π__50 a0 a1 = ()
data T__'8849'π__50
  = C_'8849''45'pure_52 | C_'8849''45'pa_54 | C_'8849''45'pe_56 |
    C_'8849''45'act_58 | C_'8849''45'ae_60 | C_'8849''45'eff_62
-- Once.Spec.Grade._·p_
d__'183'p__64 :: T_Purity_40 -> T_Purity_40 -> T_Purity_40
d__'183'p__64 v0 v1
  = case coe v0 of
      C_fin_42 v2
        -> case coe v2 of
             C_pure'7584'_36 -> coe v1
             C_act'7584'_38
               -> case coe v1 of
                    C_fin_42 v3 -> coe seq (coe v3) (coe v0)
                    C_eff_44 -> coe v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_44 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Grade.EffGrade
d_EffGrade_68 a0 = ()
data T_EffGrade_68 = C_eg'45'act_70 | C_eg'45'eff_72
-- Once.Spec.Grade.positionGrade
d_positionGrade_74 :: T_Quantity_6 -> T_Purity_40 -> T_Purity_40
d_positionGrade_74 v0 v1
  = case coe v0 of
      C_Zero_8 -> coe C_fin_42 (coe C_pure'7584'_36)
      C_One_10 -> coe v1
      C_Many_12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Grade.ArrowKind
d_ArrowKind_80 = ()
data T_ArrowKind_80 = C_mk'45'kind_90 T_Quantity_6 T_Purity_40
-- Once.Spec.Grade.ArrowKind.quantity
d_quantity_86 :: T_ArrowKind_80 -> T_Quantity_6
d_quantity_86 v0
  = case coe v0 of
      C_mk'45'kind_90 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Grade.ArrowKind.purity
d_purity_88 :: T_ArrowKind_80 -> T_Purity_40
d_purity_88 v0
  = case coe v0 of
      C_mk'45'kind_90 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
