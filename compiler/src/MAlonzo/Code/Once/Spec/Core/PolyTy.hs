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

module MAlonzo.Code.Once.Spec.Core.PolyTy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Core.PolyTy.Kind
d_Kind_8 :: ()
d_Kind_8 = erased
-- Once.Spec.Core.PolyTy.KCtx
d_KCtx_10 :: Integer -> ()
d_KCtx_10 = erased
-- Once.Spec.Core.PolyTy.Ty
d_Ty_16 a0 = ()
data T_Ty_16
  = C_var_24 MAlonzo.Code.Data.Fin.Base.T_Fin_10 | C_Unit_26 |
    C_Void_28 | C_Int_30 | C_Float_32 | C__'42'__34 T_Ty_16 T_Ty_16 |
    C__'43'__36 T_Ty_16 T_Ty_16 |
    C__'8658''91'_'93'__38 T_Ty_16
                           MAlonzo.Code.Once.Type.T_ArrowKind_40 T_Ty_16 |
    C_μ'45'type_40 T_Fun_20 |
    C_ν'45'type_42 T_Fun_20 MAlonzo.Code.Once.Type.T_Purity_32 |
    C_rigid_44 MAlonzo.Code.Once.Type.T_TKind_110 Integer
-- Once.Spec.Core.PolyTy.Fun
d_Fun_20 a0 = ()
data T_Fun_20
  = C_K_48 T_Ty_16 | C_Id_50 | C__'8853'__52 T_Fun_20 T_Fun_20 |
    C__'8855'__54 T_Fun_20 T_Fun_20
-- Once.Spec.Core.PolyTy.⟦_⟧F
d_'10214'_'10215'F_58 :: Integer -> T_Fun_20 -> T_Ty_16 -> T_Ty_16
d_'10214'_'10215'F_58 ~v0 v1 v2 = du_'10214'_'10215'F_58 v1 v2
du_'10214'_'10215'F_58 :: T_Fun_20 -> T_Ty_16 -> T_Ty_16
du_'10214'_'10215'F_58 v0 v1
  = case coe v0 of
      C_K_48 v2 -> coe v2
      C_Id_50 -> coe v1
      C__'8853'__52 v2 v3
        -> coe
             C__'43'__36 (coe du_'10214'_'10215'F_58 (coe v2) (coe v1))
             (coe du_'10214'_'10215'F_58 (coe v3) (coe v1))
      C__'8855'__54 v2 v3
        -> coe
             C__'42'__34 (coe du_'10214'_'10215'F_58 (coe v2) (coe v1))
             (coe du_'10214'_'10215'F_58 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.Sub
d_Sub_78 :: Integer -> Integer -> ()
d_Sub_78 = erased
-- Once.Spec.Core.PolyTy._⟨_⟩
d__'10216'_'10217'_88 ::
  Integer ->
  Integer ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) -> T_Ty_16
d__'10216'_'10217'_88 v0 v1 v2 v3
  = case coe v2 of
      C_var_24 v4 -> coe v3 v4
      C_Unit_26 -> coe v2
      C_Void_28 -> coe v2
      C_Int_30 -> coe v2
      C_Float_32 -> coe v2
      C__'42'__34 v4 v5
        -> coe
             C__'42'__34
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'43'__36 v4 v5
        -> coe
             C__'43'__36
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'8658''91'_'93'__38 v4 v5 v6
        -> coe
             C__'8658''91'_'93'__38
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe v5)
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v6) (coe v3))
      C_μ'45'type_40 v4
        -> coe
             C_μ'45'type_40
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v4) (coe v3))
      C_ν'45'type_42 v4 v5
        -> coe
             C_ν'45'type_42
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe v5)
      C_rigid_44 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy._⟨_⟩F
d__'10216'_'10217'F_94 ::
  Integer ->
  Integer ->
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) -> T_Fun_20
d__'10216'_'10217'F_94 v0 v1 v2 v3
  = case coe v2 of
      C_K_48 v4
        -> coe
             C_K_48
             (coe d__'10216'_'10217'_88 (coe v0) (coe v1) (coe v4) (coe v3))
      C_Id_50 -> coe v2
      C__'8853'__52 v4 v5
        -> coe
             C__'8853'__52
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v5) (coe v3))
      C__'8855'__54 v4 v5
        -> coe
             C__'8855'__54
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d__'10216'_'10217'F_94 (coe v0) (coe v1) (coe v5) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.⟦⟧F-⟨⟩
d_'10214''10215'F'45''10216''10217'_172 ::
  Integer ->
  Integer ->
  T_Fun_20 ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215'F'45''10216''10217'_172 = erased
-- Once.Spec.Core.PolyTy.⟨⟩-∘
d_'10216''10217''45''8728'_214 ::
  Integer ->
  Integer ->
  Integer ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''10217''45''8728'_214 = erased
-- Once.Spec.Core.PolyTy.⟨⟩F-∘
d_'10216''10217'F'45''8728'_230 ::
  Integer ->
  Integer ->
  Integer ->
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''10217'F'45''8728'_230 = erased
-- Once.Spec.Core.PolyTy.⌈_⌉
d_'8968'_'8969'_336 ::
  Integer -> MAlonzo.Code.Once.Type.T_Type_108 -> T_Ty_16
d_'8968'_'8969'_336 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe C_Unit_26
      MAlonzo.Code.Once.Type.C_Void_122 -> coe C_Void_28
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe
             C__'42'__34 (coe d_'8968'_'8969'_336 (coe v0) (coe v2))
             (coe d_'8968'_'8969'_336 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe
             C__'43'__36 (coe d_'8968'_'8969'_336 (coe v0) (coe v2))
             (coe d_'8968'_'8969'_336 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> coe
             C__'8658''91'_'93'__38 (coe d_'8968'_'8969'_336 (coe v0) (coe v2))
             (coe v3) (coe d_'8968'_'8969'_336 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe C_μ'45'type_40 (coe d_'8968'_'8969'F_340 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe
             C_ν'45'type_42 (coe d_'8968'_'8969'F_340 (coe v0) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.Type.C_Int_134 -> coe C_Int_30
      MAlonzo.Code.Once.Type.C_Float_136 -> coe C_Float_32
      MAlonzo.Code.Once.Type.C_rigid_138 v2 v3
        -> coe C_rigid_44 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.⌈_⌉F
d_'8968'_'8969'F_340 ::
  Integer -> MAlonzo.Code.Once.Type.T_Functor_106 -> T_Fun_20
d_'8968'_'8969'F_340 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_112 v2
        -> coe C_K_48 (coe d_'8968'_'8969'_336 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Id_114 -> coe C_Id_50
      MAlonzo.Code.Once.Type.C__'8853'__116 v2 v3
        -> coe
             C__'8853'__52 (coe d_'8968'_'8969'F_340 (coe v0) (coe v2))
             (coe d_'8968'_'8969'F_340 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8855'__118 v2 v3
        -> coe
             C__'8855'__54 (coe d_'8968'_'8969'F_340 (coe v0) (coe v2))
             (coe d_'8968'_'8969'F_340 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.GSub
d_GSub_376 :: Integer -> ()
d_GSub_376 = erased
-- Once.Spec.Core.PolyTy._⟪_⟫
d__'10218'_'10219'_382 ::
  Integer ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Type_108
d__'10218'_'10219'_382 v0 v1 v2
  = case coe v1 of
      C_var_24 v3 -> coe v2 v3
      C_Unit_26 -> coe MAlonzo.Code.Once.Type.C_Unit_120
      C_Void_28 -> coe MAlonzo.Code.Once.Type.C_Void_122
      C_Int_30 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_Float_32 -> coe MAlonzo.Code.Once.Type.C_Float_136
      C__'42'__34 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe d__'10218'_'10219'_382 (coe v0) (coe v3) (coe v2))
             (coe d__'10218'_'10219'_382 (coe v0) (coe v4) (coe v2))
      C__'43'__36 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe d__'10218'_'10219'_382 (coe v0) (coe v3) (coe v2))
             (coe d__'10218'_'10219'_382 (coe v0) (coe v4) (coe v2))
      C__'8658''91'_'93'__38 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
             (coe d__'10218'_'10219'_382 (coe v0) (coe v3) (coe v2)) (coe v4)
             (coe d__'10218'_'10219'_382 (coe v0) (coe v5) (coe v2))
      C_μ'45'type_40 v3
        -> coe
             MAlonzo.Code.Once.Type.C_μ'45'type_130
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v3) (coe v2))
      C_ν'45'type_42 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C_ν'45'type_132
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v3) (coe v2)) (coe v4)
      C_rigid_44 v3 v4
        -> coe MAlonzo.Code.Once.Type.C_rigid_138 (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy._⟪_⟫F
d__'10218'_'10219'F_386 ::
  Integer ->
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Functor_106
d__'10218'_'10219'F_386 v0 v1 v2
  = case coe v1 of
      C_K_48 v3
        -> coe
             MAlonzo.Code.Once.Type.C_K_112
             (coe d__'10218'_'10219'_382 (coe v0) (coe v3) (coe v2))
      C_Id_50 -> coe MAlonzo.Code.Once.Type.C_Id_114
      C__'8853'__52 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8853'__116
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v3) (coe v2))
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v4) (coe v2))
      C__'8855'__54 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8855'__118
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v3) (coe v2))
             (coe d__'10218'_'10219'F_386 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.⟦⟧F-⟪⟫
d_'10214''10215'F'45''10218''10219'_462 ::
  Integer ->
  T_Fun_20 ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215'F'45''10218''10219'_462 = erased
-- Once.Spec.Core.PolyTy.⌈⌉-⟪⟫
d_'8968''8969''45''10218''10219'_496 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969''45''10218''10219'_496 = erased
-- Once.Spec.Core.PolyTy.⌈⌉F-⟪⟫
d_'8968''8969'F'45''10218''10219'_504 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969'F'45''10218''10219'_504 = erased
-- Once.Spec.Core.PolyTy.⟨⟩-⟪⟫
d_'10216''10217''45''10218''10219'_586 ::
  Integer ->
  Integer ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''10217''45''10218''10219'_586 = erased
-- Once.Spec.Core.PolyTy.⟨⟩F-⟪⟫
d_'10216''10217'F'45''10218''10219'_600 ::
  Integer ->
  Integer ->
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''10217'F'45''10218''10219'_600 = erased
-- Once.Spec.Core.PolyTy.Base
d_Base_708 a0 a1 a2 = ()
data T_Base_708
  = C_b'45'var_716 | C_b'45'Unit_718 | C_b'45'Void_720 |
    C_b'45'Int_722 | C_b'45'Float_724 | C_b'45'rigid_728 |
    C_b'45'Prod_734 T_Base_708 T_Base_708 |
    C_b'45'Sum_740 T_Base_708 T_Base_708
-- Once.Spec.Core.PolyTy.WFFun
d_WFFun_746 a0 a1 a2 = ()
data T_WFFun_746
  = C_wf'45'K_754 T_Base_708 | C_wf'45'Id_756 |
    C_wf'45'Sum_762 T_WFFun_746 T_WFFun_746 |
    C_wf'45'Prod_768 T_WFFun_746 T_WFFun_746
-- Once.Spec.Core.PolyTy.Respects
d_Respects_772 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  ()
d_Respects_772 = erased
-- Once.Spec.Core.PolyTy.base-⟪⟫
d_base'45''10218''10219'_788 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T_Base_708 -> MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_base'45''10218''10219'_788 ~v0 ~v1 ~v2 v3 v4 v5
  = du_base'45''10218''10219'_788 v3 v4 v5
du_base'45''10218''10219'_788 ::
  T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T_Base_708 -> MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
du_base'45''10218''10219'_788 v0 v1 v2
  = case coe v2 of
      C_b'45'var_716
        -> case coe v0 of
             C_var_24 v5 -> coe v1 v5 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      C_b'45'Unit_718
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
      C_b'45'Void_720
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200
      C_b'45'Int_722
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202
      C_b'45'Float_724
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204
      C_b'45'rigid_728
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'rigid_220
      C_b'45'Prod_734 v5 v6
        -> case coe v0 of
             C__'42'__34 v7 v8
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
                    (coe du_base'45''10218''10219'_788 (coe v7) (coe v1) (coe v5))
                    (coe du_base'45''10218''10219'_788 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_b'45'Sum_740 v5 v6
        -> case coe v0 of
             C__'43'__36 v7 v8
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216
                    (coe du_base'45''10218''10219'_788 (coe v7) (coe v1) (coe v5))
                    (coe du_base'45''10218''10219'_788 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.wf-⟪⟫
d_wf'45''10218''10219'_826 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T_WFFun_746 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
d_wf'45''10218''10219'_826 ~v0 ~v1 ~v2 v3 v4 v5
  = du_wf'45''10218''10219'_826 v3 v4 v5
du_wf'45''10218''10219'_826 ::
  T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T_WFFun_746 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
du_wf'45''10218''10219'_826 v0 v1 v2
  = case coe v2 of
      C_wf'45'K_754 v4
        -> case coe v0 of
             C_K_48 v5
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240
                    (coe du_base'45''10218''10219'_788 (coe v5) (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_wf'45'Id_756
        -> coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
      C_wf'45'Sum_762 v5 v6
        -> case coe v0 of
             C__'8853'__52 v7 v8
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248
                    (coe du_wf'45''10218''10219'_826 (coe v7) (coe v1) (coe v5))
                    (coe du_wf'45''10218''10219'_826 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_wf'45'Prod_768 v5 v6
        -> case coe v0 of
             C__'8855'__54 v7 v8
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254
                    (coe du_wf'45''10218''10219'_826 (coe v7) (coe v1) (coe v5))
                    (coe du_wf'45''10218''10219'_826 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.Schema
d_Schema_846 = ()
data T_Schema_846
  = C_schema_860 Integer
                 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                  MAlonzo.Code.Once.Type.T_TKind_110)
                 T_Ty_16
-- Once.Spec.Core.PolyTy.Schema.arity
d_arity_854 :: T_Schema_846 -> Integer
d_arity_854 v0
  = case coe v0 of
      C_schema_860 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.Schema.kinds
d_kinds_856 ::
  T_Schema_846 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_TKind_110
d_kinds_856 v0
  = case coe v0 of
      C_schema_860 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.Schema.type
d_type_858 :: T_Schema_846 -> T_Ty_16
d_type_858 v0
  = case coe v0 of
      C_schema_860 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTy.Sig
d_Sig_864 a0 a1 = ()
data T_Sig_864
  = C_'91''93'_868 | C__'9655'__872 T_Sig_864 T_Schema_846
-- Once.Spec.Core.PolyTy.sigOf
d_sigOf_878 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_Sig_864 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigOf_878 v0 ~v1 ~v2 = du_sigOf_878 v0
du_sigOf_878 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_sigOf_878 v0 = coe v0
-- Once.Spec.Core.PolyTy._!!_
d__'33''33'__886 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  T_Sig_864 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Schema_846
d__'33''33'__886 ~v0 ~v1 v2 v3 = du__'33''33'__886 v2 v3
du__'33''33'__886 ::
  T_Sig_864 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Schema_846
du__'33''33'__886 v0 v1
  = case coe v0 of
      C__'9655'__872 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du__'33''33'__886 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
