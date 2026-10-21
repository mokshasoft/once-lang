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

module MAlonzo.Code.Once.TypeCheck.TargetView where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.TypeCheck.TargetView.CataTarget
d_CataTarget_6 a0 = ()
data T_CataTarget_6 = C_cata'45'at_14 | C_cata'45'other_18
-- Once.TypeCheck.TargetView.cataTarget
d_cataTarget_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CataTarget_6
d_cataTarget_22 v0
  = let v1 = coe C_cata'45'other_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_cata'45'at_14
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.AnaTarget
d_AnaTarget_30 a0 = ()
data T_AnaTarget_30
  = C_loop'45'at_36 |
    C_ana'45'at_46 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_ana'45'other_50
-- Once.TypeCheck.TargetView.anaTarget
d_anaTarget_54 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_AnaTarget_30
d_anaTarget_54 v0
  = let v1 = coe C_ana'45'other_50 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v6 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                                              -> coe
                                                   C_ana'45'at_46
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54)
                                            _ -> coe v1
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                                              -> coe
                                                   C_ana'45'at_46
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58)
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44 -> coe C_loop'45'at_36
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.InTarget
d_InTarget_72 a0 = ()
data T_InTarget_72 = C_in'45'at_76 | C_in'45'other_80
-- Once.TypeCheck.TargetView.inTarget
d_inTarget_84 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_InTarget_72
d_inTarget_84 v0
  = let v1 = coe C_in'45'other_80 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v2
           -> coe C_in'45'at_76
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CurryTarget
d_CurryTarget_88 a0 = ()
data T_CurryTarget_88 = C_curry'45'at_100 | C_curry'45'other_104
-- Once.TypeCheck.TargetView.curryTarget
d_curryTarget_108 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CurryTarget_88
d_curryTarget_108 v0
  = let v1 = coe C_curry'45'other_104 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v7 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> coe C_curry'45'at_100
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.PairTarget
d_PairTarget_120 a0 = ()
data T_PairTarget_120 = C_pair'45'at_130 | C_pair'45'other_134
-- Once.TypeCheck.TargetView.pairTarget
d_pairTarget_138 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_PairTarget_120
d_pairTarget_138 v0
  = let v1 = coe C_pair'45'other_134 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
                                -> coe C_pair'45'at_130
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CaseTarget
d_CaseTarget_148 a0 = ()
data T_CaseTarget_148 = C_case'45'at_158 | C_case'45'other_162
-- Once.TypeCheck.TargetView.caseTarget
d_caseTarget_166 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CaseTarget_148
d_caseTarget_166 v0
  = let v1 = coe C_case'45'other_162 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_case'45'at_158
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ArrowTarget
d_ArrowTarget_176 a0 = ()
data T_ArrowTarget_176 = C_arrow'45'at_184 | C_arrow'45'other_188
-- Once.TypeCheck.TargetView.arrowTarget
d_arrowTarget_192 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_ArrowTarget_176
d_arrowTarget_192 v0
  = let v1 = coe C_arrow'45'other_188 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_arrow'45'at_184
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.SumTarget
d_SumTarget_200 a0 = ()
data T_SumTarget_200 = C_sum'45'at_206 | C_sum'45'other_210
-- Once.TypeCheck.TargetView.NuView
d_NuView_212 a0 = ()
data T_NuView_212 = C_nu'45'at_218 | C_nu'45'other_222
-- Once.TypeCheck.TargetView.nuView
d_nuView_226 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_NuView_212
d_nuView_226 v0
  = let v1 = coe C_nu'45'other_222 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v2 v3
           -> coe C_nu'45'at_218
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ApplyView
d_ApplyView_232 a0 = ()
data T_ApplyView_232 = C_apply'45'at_242 | C_apply'45'other_246
-- Once.TypeCheck.TargetView.applyView
d_applyView_250 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_ApplyView_232
d_applyView_250 v0
  = let v1 = coe C_apply'45'other_246 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'42'__24 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v4 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_apply'45'at_242
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ProdView
d_ProdView_260 a0 = ()
data T_ProdView_260 = C_prod'45'at_266 | C_prod'45'other_270
-- Once.TypeCheck.TargetView.prodView
d_prodView_274 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_ProdView_260
d_prodView_274 v0
  = let v1 = coe C_prod'45'other_270 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'42'__24 v2 v3
           -> coe C_prod'45'at_266
         _ -> coe v1)
