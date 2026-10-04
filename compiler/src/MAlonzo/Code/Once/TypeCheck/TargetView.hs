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
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.TargetView.CataTarget
d_CataTarget_6 a0 = ()
data T_CataTarget_6 = C_cata'45'at_14 | C_cata'45'other_18
-- Once.TypeCheck.TargetView.cataTarget
d_cataTarget_22 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CataTarget_6
d_cataTarget_22 v0
  = let v1 = coe C_cata'45'other_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Once.Type.C_Many_10 -> coe C_cata'45'at_14
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.AnaTarget
d_AnaTarget_30 a0 = ()
data T_AnaTarget_30 = C_ana'45'at_40 | C_ana'45'other_44
-- Once.TypeCheck.TargetView.anaTarget
d_anaTarget_48 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_AnaTarget_30
d_anaTarget_48 v0
  = let v1 = coe C_ana'45'other_44 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_ν'45'type_132 v7 v8 -> coe C_ana'45'at_40
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.InTarget
d_InTarget_58 a0 = ()
data T_InTarget_58 = C_in'45'at_62 | C_in'45'other_66
-- Once.TypeCheck.TargetView.inTarget
d_inTarget_70 :: MAlonzo.Code.Once.Type.T_Type_108 -> T_InTarget_58
d_inTarget_70 v0
  = let v1 = coe C_in'45'other_66 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_μ'45'type_130 v2 -> coe C_in'45'at_62
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CurryTarget
d_CurryTarget_74 a0 = ()
data T_CurryTarget_74 = C_curry'45'at_86 | C_curry'45'other_90
-- Once.TypeCheck.TargetView.curryTarget
d_curryTarget_94 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CurryTarget_74
d_curryTarget_94 v0
  = let v1 = coe C_curry'45'other_90 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Once.Type.C_Many_10 -> coe C_curry'45'at_86
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.PairTarget
d_PairTarget_106 a0 = ()
data T_PairTarget_106 = C_pair'45'at_116 | C_pair'45'other_120
-- Once.TypeCheck.TargetView.pairTarget
d_pairTarget_124 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_PairTarget_106
d_pairTarget_124 v0
  = let v1 = coe C_pair'45'other_120 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C__'42'__124 v7 v8 -> coe C_pair'45'at_116
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.CaseTarget
d_CaseTarget_134 a0 = ()
data T_CaseTarget_134 = C_case'45'at_144 | C_case'45'other_148
-- Once.TypeCheck.TargetView.caseTarget
d_caseTarget_152 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CaseTarget_134
d_caseTarget_152 v0
  = let v1 = coe C_case'45'other_148 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Many_10 -> coe C_case'45'at_144
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ArrowTarget
d_ArrowTarget_162 a0 = ()
data T_ArrowTarget_162 = C_arrow'45'at_170 | C_arrow'45'other_174
-- Once.TypeCheck.TargetView.arrowTarget
d_arrowTarget_178 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_ArrowTarget_162
d_arrowTarget_178 v0
  = let v1 = coe C_arrow'45'other_174 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10 -> coe C_arrow'45'at_170
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.TargetView.SumTarget
d_SumTarget_186 a0 = ()
data T_SumTarget_186 = C_sum'45'at_192 | C_sum'45'other_196
-- Once.TypeCheck.TargetView.sumTarget
d_sumTarget_200 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_SumTarget_186
d_sumTarget_200 v0
  = let v1 = coe C_sum'45'other_196 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'43'__126 v2 v3 -> coe C_sum'45'at_192
         _ -> coe v1)
-- Once.TypeCheck.TargetView.NuView
d_NuView_206 a0 = ()
data T_NuView_206 = C_nu'45'at_212 | C_nu'45'other_216
-- Once.TypeCheck.TargetView.nuView
d_nuView_220 :: MAlonzo.Code.Once.Type.T_Type_108 -> T_NuView_206
d_nuView_220 v0
  = let v1 = coe C_nu'45'other_216 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3 -> coe C_nu'45'at_212
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ApplyView
d_ApplyView_226 a0 = ()
data T_ApplyView_226 = C_apply'45'at_236 | C_apply'45'other_240
-- Once.TypeCheck.TargetView.applyView
d_applyView_244 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_ApplyView_226
d_applyView_244 v0
  = let v1 = coe C_apply'45'other_240 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v4 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Many_10 -> coe C_apply'45'at_236
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.TargetView.ProdView
d_ProdView_254 a0 = ()
data T_ProdView_254 = C_prod'45'at_260 | C_prod'45'other_264
-- Once.TypeCheck.TargetView.prodView
d_prodView_268 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_ProdView_254
d_prodView_268 v0
  = let v1 = coe C_prod'45'other_264 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'42'__124 v2 v3 -> coe C_prod'45'at_260
         _ -> coe v1)
