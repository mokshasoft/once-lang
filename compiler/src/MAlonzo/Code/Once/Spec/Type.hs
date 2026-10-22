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

module MAlonzo.Code.Once.Spec.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Spec.Type.Ty
d_Ty_8 a0 = ()
data T_Ty_8
  = C_var_16 MAlonzo.Code.Data.Fin.Base.T_Fin_10 | C_Unit_18 |
    C_Void_20 | C__'42'__22 T_Ty_8 T_Ty_8 | C__'43'__24 T_Ty_8 T_Ty_8 |
    C__'8658''91'_'93'__26 T_Ty_8
                           MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 T_Ty_8 |
    C_μ_28 T_Fun_12 |
    C_ν_30 T_Fun_12 MAlonzo.Code.Once.Spec.Grade.T_Finite_34 |
    C_Int_32 | C_Float_34
-- Once.Spec.Type.Fun
d_Fun_12 a0 = ()
data T_Fun_12
  = C_K_38 T_Ty_8 | C_Id_40 | C__'8853'__42 T_Fun_12 T_Fun_12 |
    C__'8855'__44 T_Fun_12 T_Fun_12
-- Once.Spec.Type.Type
d_Type_46 :: ()
d_Type_46 = erased
-- Once.Spec.Type.⟦_⟧F
d_'10214'_'10215'F_50 :: Integer -> T_Fun_12 -> T_Ty_8 -> T_Ty_8
d_'10214'_'10215'F_50 ~v0 v1 v2 = du_'10214'_'10215'F_50 v1 v2
du_'10214'_'10215'F_50 :: T_Fun_12 -> T_Ty_8 -> T_Ty_8
du_'10214'_'10215'F_50 v0 v1
  = case coe v0 of
      C_K_38 v2 -> coe v2
      C_Id_40 -> coe v1
      C__'8853'__42 v2 v3
        -> coe
             C__'43'__24 (coe du_'10214'_'10215'F_50 (coe v2) (coe v1))
             (coe du_'10214'_'10215'F_50 (coe v3) (coe v1))
      C__'8855'__44 v2 v3
        -> coe
             C__'42'__22 (coe du_'10214'_'10215'F_50 (coe v2) (coe v1))
             (coe du_'10214'_'10215'F_50 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Kind
d_Kind_70 = ()
data T_Kind_70 = C_base_72 | C_any_74
-- Once.Spec.Type.KCtx
d_KCtx_76 :: Integer -> ()
d_KCtx_76 = erased
-- Once.Spec.Type.Base
d_Base_84 a0 a1 a2 = ()
data T_Base_84
  = C_b'45'var_92 | C_b'45'Unit_94 | C_b'45'Void_96 | C_b'45'Int_98 |
    C_b'45'Float_100 | C_b'45''42'_106 T_Base_84 T_Base_84 |
    C_b'45''43'_112 T_Base_84 T_Base_84
-- Once.Spec.Type.WFFun
d_WFFun_118 a0 a1 a2 = ()
data T_WFFun_118
  = C_wf'45'K_126 T_Base_84 | C_wf'45'Id_128 |
    C_wf'45''8853'_134 T_WFFun_118 T_WFFun_118 |
    C_wf'45''8855'_140 T_WFFun_118 T_WFFun_118
-- Once.Spec.Type.∅ₖ
d_'8709''8342'_142 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Kind_70
d_'8709''8342'_142 ~v0 = du_'8709''8342'_142
du_'8709''8342'_142 :: T_Kind_70
du_'8709''8342'_142 = MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.TySub
d_TySub_144 :: Integer -> Integer -> ()
d_TySub_144 = erased
-- Once.Spec.Type._⟨_⟩
d__'10216'_'10217'_154 ::
  Integer ->
  Integer ->
  T_Ty_8 -> (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_8) -> T_Ty_8
d__'10216'_'10217'_154 v0 v1 v2 v3
  = case coe v2 of
      C_var_16 v4 -> coe v3 v4
      C_Unit_18 -> coe v2
      C_Void_20 -> coe v2
      C__'42'__22 v4 v5
        -> coe
             C__'42'__22
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'43'__24 v4 v5
        -> coe
             C__'43'__24
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'8658''91'_'93'__26 v4 v5 v6
        -> coe
             C__'8658''91'_'93'__26
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe v5)
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v6) (coe v3))
      C_μ_28 v4
        -> coe
             C_μ_28
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v4) (coe v3))
      C_ν_30 v4 v5
        -> coe
             C_ν_30
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe v5)
      C_Int_32 -> coe v2
      C_Float_34 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type._⟨_⟩F
d__'10216'_'10217'F_160 ::
  Integer ->
  Integer ->
  T_Fun_12 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_8) -> T_Fun_12
d__'10216'_'10217'F_160 v0 v1 v2 v3
  = case coe v2 of
      C_K_38 v4
        -> coe
             C_K_38
             (coe d__'10216'_'10217'_154 (coe v0) (coe v1) (coe v4) (coe v3))
      C_Id_40 -> coe v2
      C__'8853'__42 v4 v5
        -> coe
             C__'8853'__42
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'8855'__44 v4 v5
        -> coe
             C__'8855'__44
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'F_160 (coe v0) (coe v1) (coe v5) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Respects
d_Respects_226 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Kind_70) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Kind_70) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_8) -> ()
d_Respects_226 = erased
-- Once.Spec.Type.Occurs
d_Occurs_240 a0 a1 a2 = ()
data T_Occurs_240
  = C_o'45'var_250 | C_o'45''42''737'_256 T_Occurs_240 |
    C_o'45''42''691'_262 T_Occurs_240 |
    C_o'45''43''737'_268 T_Occurs_240 |
    C_o'45''43''691'_274 T_Occurs_240 |
    C_o'45''8658''737'_282 T_Occurs_240 |
    C_o'45''8658''691'_290 T_Occurs_240 | C_o'45'μ_294 T_OccursF_246 |
    C_o'45'ν_300 T_OccursF_246
-- Once.Spec.Type.OccursF
d_OccursF_246 a0 a1 a2 = ()
data T_OccursF_246
  = C_o'45'K_306 T_Occurs_240 |
    C_o'45''8853''737'_312 T_OccursF_246 |
    C_o'45''8853''691'_318 T_OccursF_246 |
    C_o'45''8855''737'_324 T_OccursF_246 |
    C_o'45''8855''691'_330 T_OccursF_246
