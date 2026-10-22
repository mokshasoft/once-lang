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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.TypeCheck.TargetView.CataTarget
d_CataTarget_8 a0 a1 = ()
data T_CataTarget_8 = C_cata'45'at_18 | C_cata'45'other_22
-- Once.TypeCheck.TargetView.cataTarget
d_cataTarget_28 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CataTarget_8
d_cataTarget_28 ~v0 v1 = du_cataTarget_28 v1
du_cataTarget_28 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CataTarget_8
du_cataTarget_28 v0
  = let v1 = coe C_cata'45'other_22 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Type.C_μ_28 v5
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_cata'45'at_18
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.AnaTarget
d_AnaTarget_38 a0 a1 = ()
data T_AnaTarget_38
  = C_loop'45'at_46 |
    C_ana'45'at_56 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_ana'45'other_60
-- Once.TypeCheck.TargetView.anaTarget
d_anaTarget_66 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_AnaTarget_38
d_anaTarget_66 ~v0 v1 = du_anaTarget_66 v1
du_anaTarget_66 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_AnaTarget_38
du_anaTarget_66 v0
  = let v1 = coe C_ana'45'other_60 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v6 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Spec.Type.C_ν_30 v8 v9
                                              -> coe
                                                   C_ana'45'at_56
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54)
                                            _ -> coe v1
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Spec.Type.C_ν_30 v8 v9
                                              -> coe
                                                   C_ana'45'at_56
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58)
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44 -> coe C_loop'45'at_46
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.InTarget
d_InTarget_86 a0 a1 = ()
data T_InTarget_86 = C_in'45'at_92 | C_in'45'other_96
-- Once.TypeCheck.TargetView.inTarget
d_inTarget_102 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InTarget_86
d_inTarget_102 ~v0 v1 = du_inTarget_102 v1
du_inTarget_102 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InTarget_86
du_inTarget_102 v0
  = let v1 = coe C_in'45'other_96 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_μ_28 v2 -> coe C_in'45'at_92
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CurryTarget
d_CurryTarget_108 a0 a1 = ()
data T_CurryTarget_108 = C_curry'45'at_122 | C_curry'45'other_126
-- Once.TypeCheck.TargetView.curryTarget
d_curryTarget_132 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CurryTarget_108
d_curryTarget_132 ~v0 v1 = du_curryTarget_132 v1
du_curryTarget_132 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CurryTarget_108
du_curryTarget_132 v0
  = let v1 = coe C_curry'45'other_126 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> coe C_curry'45'at_122
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.PairTarget
d_PairTarget_146 a0 a1 = ()
data T_PairTarget_146 = C_pair'45'at_158 | C_pair'45'other_162
-- Once.TypeCheck.TargetView.pairTarget
d_pairTarget_168 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_PairTarget_146
d_pairTarget_168 ~v0 v1 = du_pairTarget_168 v1
du_pairTarget_168 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_PairTarget_146
du_pairTarget_168 v0
  = let v1 = coe C_pair'45'other_162 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
                                -> coe C_pair'45'at_158
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CaseTarget
d_CaseTarget_180 a0 a1 = ()
data T_CaseTarget_180 = C_case'45'at_192 | C_case'45'other_196
-- Once.TypeCheck.TargetView.caseTarget
d_caseTarget_202 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CaseTarget_180
d_caseTarget_202 ~v0 v1 = du_caseTarget_202 v1
du_caseTarget_202 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CaseTarget_180
du_caseTarget_202 v0
  = let v1 = coe C_case'45'other_196 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v5 v6
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_case'45'at_192
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ArrowTarget
d_ArrowTarget_214 a0 a1 = ()
data T_ArrowTarget_214 = C_arrow'45'at_224 | C_arrow'45'other_228
-- Once.TypeCheck.TargetView.arrowTarget
d_arrowTarget_234 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ArrowTarget_214
d_arrowTarget_234 ~v0 v1 = du_arrowTarget_234 v1
du_arrowTarget_234 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ArrowTarget_214
du_arrowTarget_234 v0
  = let v1 = coe C_arrow'45'other_228 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_arrow'45'at_224
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.SumTarget
d_SumTarget_244 a0 a1 = ()
data T_SumTarget_244 = C_sum'45'at_252 | C_sum'45'other_256
-- Once.TypeCheck.TargetView.NuView
d_NuView_260 a0 a1 = ()
data T_NuView_260 = C_nu'45'at_268 | C_nu'45'other_272
-- Once.TypeCheck.TargetView.nuView
d_nuView_278 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NuView_260
d_nuView_278 ~v0 v1 = du_nuView_278 v1
du_nuView_278 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NuView_260
du_nuView_278 v0
  = let v1 = coe C_nu'45'other_272 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3 -> coe C_nu'45'at_268
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ApplyView
d_ApplyView_286 a0 a1 = ()
data T_ApplyView_286 = C_apply'45'at_298 | C_apply'45'other_302
-- Once.TypeCheck.TargetView.applyView
d_applyView_308 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ApplyView_286
d_applyView_308 ~v0 v1 = du_applyView_308 v1
du_applyView_308 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ApplyView_286
du_applyView_308 v0
  = let v1 = coe C_apply'45'other_302 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe C_apply'45'at_298
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ProdView
d_ProdView_320 a0 a1 = ()
data T_ProdView_320 = C_prod'45'at_328 | C_prod'45'other_332
-- Once.TypeCheck.TargetView.prodView
d_prodView_338 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ProdView_320
d_prodView_338 ~v0 v1 = du_prodView_338 v1
du_prodView_338 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_ProdView_320
du_prodView_338 v0
  = let v1 = coe C_prod'45'other_332 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe C_prod'45'at_328
         _ -> coe v1)
