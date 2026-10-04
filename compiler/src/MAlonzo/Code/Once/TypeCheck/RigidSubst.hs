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

module MAlonzo.Code.Once.TypeCheck.RigidSubst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.RigidSubst.ρ̂
d_ρ'770'_14 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_ρ'770'_14 v0 v1 v2 ~v3 v4 = du_ρ'770'_14 v0 v1 v2 v4
du_ρ'770'_14 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_ρ'770'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
-- Once.TypeCheck.RigidSubst.ρ̂F
d_ρ'770'F_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106
d_ρ'770'F_18 v0 v1 v2 ~v3 v4 = du_ρ'770'F_18 v0 v1 v2 v4
du_ρ'770'F_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106
du_ρ'770'F_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'F_386 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
-- Once.TypeCheck.RigidSubst.ρ̂-⟦⟧
d_ρ'770''45''10214''10215'_26 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45''10214''10215'_26 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-base
d_ρ'770''45'base_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_ρ'770''45'base_36 v0 v1 ~v2 v3 v4 v5
  = du_ρ'770''45'base_36 v0 v1 v3 v4 v5
du_ρ'770''45'base_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
du_ρ'770''45'base_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.du_base'45''10218''10219'_788
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'base_318 (coe v0)
         (coe v1) (coe v3) (coe v4))
-- Once.TypeCheck.RigidSubst.ρ̂-wf
d_ρ'770''45'wf_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
d_ρ'770''45'wf_42 v0 v1 ~v2 v3 v4 v5
  = du_ρ'770''45'wf_42 v0 v1 v3 v4 v5
du_ρ'770''45'wf_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
du_ρ'770''45'wf_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'wf_352 (coe v0) (coe v1)
         (coe v3) (coe v4))
-- Once.TypeCheck.RigidSubst.ρ̂-rf
d_ρ'770''45'rf_48 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'rf_48 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-<:
d_ρ'770''45''60''58'_60 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_ρ'770''45''60''58'_60 v0 v1 v2 ~v3 v4 v5 v6
  = du_ρ'770''45''60''58'_60 v0 v1 v2 v4 v5 v6
du_ρ'770''45''60''58'_60 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_ρ'770''45''60''58'_60 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54 -> coe v5
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56 -> coe v5
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58 -> coe v5
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v13 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v19)
                              (coe v16) (coe v13))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v18)
                              (coe v21) (coe v14))
                           v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__124 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v9
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v9
      MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_112
        -> coe
             MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.substPoly-ρ̂
d_substPoly'45'ρ'770'_88 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substPoly'45'ρ'770'_88 = erased
-- Once.TypeCheck.RigidSubst.substPolyF-ρ̂
d_substPolyF'45'ρ'770'_96 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substPolyF'45'ρ'770'_96 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-ki
d_ρ'770''45'ki_178 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ρ'770''45'ki_178 v0 v1 v2 v3 ~v4 ~v5 v6
  = du_ρ'770''45'ki_178 v0 v1 v2 v3 v6
du_ρ'770''45'ki_178 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ρ'770''45'ki_178 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       (\ v9 -> coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v5 v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe
                          (\ v9 v10 ->
                             coe
                               du_ρ'770''45'base_36 (coe v0) (coe v1) (coe v3) (coe v5 v9)
                               (coe v8 v9 v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.ρ̂S
d_ρ'770'S_194 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d_ρ'770'S_194 v0 v1 v2 ~v3 ~v4 v5 = du_ρ'770'S_194 v0 v1 v2 v5
du_ρ'770'S_194 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
du_ρ'770'S_194 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8 -> coe v3
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
             (coe du_ρ'770'S_194 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v6)) v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.ρ̂N
d_ρ'770'N_202 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_ρ'770'N_202 v0 v1 v2 ~v3 v4 = du_ρ'770'N_202 v0 v1 v2 v4
du_ρ'770'N_202 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
du_ρ'770'N_202 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v4))
                (coe
                   du_ρ'770'_14 (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.TypeCheck.Context.d_type_16 (coe v4)))
                (coe MAlonzo.Code.Once.TypeCheck.Context.d_quantity_18 (coe v4)))
             (coe du_ρ'770'N_202 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.ρ̂C
d_ρ'770'C_208 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ρ'770'C_208 v0 v1 v2 ~v3 v4 = du_ρ'770'C_208 v0 v1 v2 v4
du_ρ'770'C_208 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
du_ρ'770'C_208 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404 v4 v5 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404 (coe v4)
             (coe du_ρ'770'N_202 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe du_ρ'770'S_194 (coe v0) (coe v1) (coe v2) (coe v6)) (coe v7)
             (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.lookup-ρ̂
d_lookup'45'ρ'770'_228 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'ρ'770'_228 = erased
-- Once.TypeCheck.RigidSubst.lk-just
d_lk'45'just_254 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk'45'just_254 = erased
-- Once.TypeCheck.RigidSubst.lk-nothing
d_lk'45'nothing_376 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk'45'nothing_376 = erased
-- Once.TypeCheck.RigidSubst.lkL-nothing
d_lkL'45'nothing_478 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lkL'45'nothing_478 = erased
-- Once.TypeCheck.RigidSubst.ImportsRF
d_ImportsRF_494 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_ImportsRF_494 = erased
-- Once.TypeCheck.RigidSubst._⇝ᵢ_
d__'8669''7522'__512 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d__'8669''7522'__512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du__'8669''7522'__512 v10
du__'8669''7522'__512 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du__'8669''7522'__512 v0 = coe v0
-- Once.TypeCheck.RigidSubst._⇝ᶜ_
d__'8669''7580'__526 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d__'8669''7580'__526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du__'8669''7580'__526 v10
du__'8669''7580'__526 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du__'8669''7580'__526 v0 = coe v0
-- Once.TypeCheck.RigidSubst.subst-i
d_subst'45'i_538 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_subst'45'i_538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404 v10 v11 v12 v13 v14 v15
        -> coe
             d_subst'45'i'8242'_582 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-c
d_subst'45'c_548 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_subst'45'c_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404 v10 v11 v12 v13 v14 v15
        -> coe
             d_subst'45'c'8242'_602 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-d
d_subst'45'd_562 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
d_subst'45'd_562 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404 v12 v13 v14 v15 v16 v17
        -> coe
             d_subst'45'd'8242'_626 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-i′
d_subst'45'i'8242'_582 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_subst'45'i'8242'_582 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v19
        -> case coe v19 of
             MAlonzo.Code.Once.Surface.Context.C_svar_218 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62
                    (coe MAlonzo.Code.Once.Surface.Context.C_svar_218 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v20
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v20
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v18 v20
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v18
             v20
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v21
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v21
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104 v18 v19 v20 v21 v25
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104
             v18 v19 v20 v21 v25
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v21 v22
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v19
                    (d_subst'45'c'8242'_602
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v12) (coe v13)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v26 v27
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v20 v21
                           (d_subst'45'i'8242'_582
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v24) (coe v26) (coe v20) (coe v13)
                              (coe v22))
                           (d_subst'45'i'8242'_582
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v25) (coe v27) (coe v21) (coe v13)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v18
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v20)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v13)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v19 v21 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v19)) v21 v22 v23
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v27) (coe v19) (coe v22) (coe v13)
                       (coe v24))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20 (coe v26)
                             (coe v19) (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v19
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v7) (coe v8) (coe v9) (coe v28) (coe v11)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v23)
                       (coe v13) (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v32 v33 v34 v35 v36
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v21))
                       (coe v2))
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v22))
                       (coe v2))
                    v24 v25 v26 v27 v28
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v32)
                       (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v21) (coe v22))
                       (coe v26) (coe v13) (coe v29))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20 (coe v33)
                             (coe v21) (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v21
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v7) (coe v8) (coe v9) (coe v34) (coe v11)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v24 v27)
                       (coe v13) (coe v30))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20 (coe v35)
                             (coe v22) (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v22
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v7) (coe v8) (coe v9) (coe v36) (coe v11)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v25 v28)
                       (coe v13) (coe v31))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v19
                    v20
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228
                    v19 v20
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242
                    v19 v20
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256
                    v19 v20
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v19
                    v20
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v18
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v18))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v11) (coe v18))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v17) (coe v11))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v17 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17)) v18
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v17) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v23 v24 v25
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338
                           (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                                 (coe v17))
                              (coe v2))
                           v19
                           (d_subst'45'i'8242'_582
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v17)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v25))
                                 (coe v17))
                              (coe v19) (coe v13) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350 v17 v19 v20 v22
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350
                    (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19
                    (coe
                       du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17) (coe v20))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v17)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v19) (coe v13) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362 v17 v19 v20 v22
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362
                    (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19
                    (coe
                       du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17) (coe v20))
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v17)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                       (coe v19) (coe v13) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380 v18 v20 v21 v22 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v26 v27
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v18))
                       (coe v2))
                    v20 v21 v22
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v18)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v20)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v11))
                       (coe v21) (coe v13) (coe v24))
                    (d_subst'45'c'8242'_602
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v27) (coe v18) (coe v22) (coe v13)
                       (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396 v18 v20 v21 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v27 v28 v29
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396
                           (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                                 (coe v18))
                              (coe v2))
                           v20 v21
                           (d_subst'45'i'8242'_582
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v25)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v18)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v29))
                              (coe v20) (coe v13) (coe v23))
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v26) (coe v18) (coe v21) (coe v13)
                              (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412 v18 v20 v21 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v18)) v20 v21
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26) (coe v18) (coe v21) (coe v13)
                       (coe v23))
                    (d_subst'45'd'8242'_626
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25) (coe v18)
                       (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v11) (coe v20)
                       (coe v13) (coe v24))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-c′
d_subst'45'c'8242'_602 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_subst'45'c'8242'_602 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v19 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v33 v34
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496
                                         (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v19)) v22
                                         v23
                                         (d_subst'45'd'8242'_626
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v27) (coe v30)
                                            (coe v34) (coe v19) (coe v23) (coe v13) (coe v24))
                                         (d_subst'45'c'8242'_602
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v29)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v34))
                                               (coe v32))
                                            (coe v22) (coe v13) (coe v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v19 v21 v23 v24 v25 v26 v27 v28
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v29 v30
               -> case coe v29 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v31 v32
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v33 v34 v35
                             -> case coe v34 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v36 v37
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520
                                         (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0)
                                               (coe v1) (coe v19))
                                            (coe v2))
                                         (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0)
                                               (coe v1) (coe v21))
                                            (coe v2))
                                         v23 v24 v25
                                         (d_subst'45'i'8242'_582
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v32)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v21))
                                            (coe v24) (coe v13) (coe v26))
                                         (coe
                                            du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v21))
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v37))
                                               (coe v35))
                                            (coe v27))
                                         (d_subst'45'c'8242'_602
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v30)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v33)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v37))
                                               (coe v19))
                                            (coe v25) (coe v13) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v30 v31 v32
                             -> case coe v30 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v33 v34
                                    -> case coe v31 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540
                                                v22 v23
                                                (d_subst'45'c'8242'_602
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v33)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v36))
                                                      (coe v32))
                                                   (coe v22) (coe v13) (coe v24))
                                                (d_subst'45'c'8242'_602
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v27)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v34)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v36))
                                                      (coe v32))
                                                   (coe v23) (coe v13) (coe v25))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v33 v34
                                    -> case coe v32 of
                                         MAlonzo.Code.Once.Type.C__'42'__124 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560
                                                v22 v23
                                                (d_subst'45'c'8242'_602
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v34))
                                                      (coe v35))
                                                   (coe v22) (coe v13) (coe v24))
                                                (d_subst'45'c'8242'_602
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v27)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v34))
                                                      (coe v36))
                                                   (coe v23) (coe v13) (coe v25))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v26 v27 v28
                      -> case coe v28 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v29 v30 v31
                             -> case coe v30 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v32 v33
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578
                                         (d_subst'45'c'8242'_602
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v25)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__124 (coe v26)
                                                  (coe v29))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v33))
                                               (coe v31))
                                            (coe v12) (coe v13) (coe v23))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v21 v22
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v25 v26 v27
                      -> case coe v25 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v28
                             -> case coe v26 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v29 v30
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592
                                         (coe
                                            du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v28)
                                            (coe v21))
                                         (d_subst'45'c'8242'_602
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v24)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                  (coe v28) (coe v27))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v30))
                                               (coe v27))
                                            (coe v12) (coe v13) (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_606 v21 v22
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v25 v26 v27
                      -> case coe v27 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v28 v29
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_606
                                  (coe
                                     du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v28)
                                     (coe v21))
                                  (d_subst'45'c'8242'_602
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe (0 :: Integer)) (coe v8) (coe v9) (coe v24)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v25)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v29))
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v28)
                                           (coe v25)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                              (coe v8) (coe v9))))
                                     (coe v13) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v17 v20 v21
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17))
             (d_subst'45'i'8242'_582
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v10) (coe v17) (coe v12) (coe v13)
                (coe v20))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v17)
                (coe v11) (coe v21))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638 v21 v25
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v26 v27
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v28 v29 v30
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638 v21
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe addInt (coe (1 :: Integer)) (coe v4))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20 (coe v26)
                                    (coe v28) (coe MAlonzo.Code.Once.Type.C_Many_10))
                                 (coe v5))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v28
                                 (coe MAlonzo.Code.Once.Type.C_Many_10))
                              (coe v7) (coe v8) (coe v9) (coe v27) (coe v30)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v12)
                              (coe v13) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_654 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v26 v27
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_654
                           v20 v21
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v24) (coe v26) (coe v20) (coe v13)
                              (coe v22))
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v25) (coe v27) (coe v21) (coe v13)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_664 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v23
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_664
                           v18
                           (coe
                              du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v23) (coe v19))
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v23) (coe v11))
                              (coe v18) (coe v13) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_676 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_676
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_688 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_688
                           v19
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v23) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_700 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_700
                           v19
                           (d_subst'45'c'8242'_602
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v24) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_710 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_710
                    v18
                    (d_subst'45'c'8242'_602
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724 v18 v19 v20 v25
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724
             v18 v19 v20
             (coe
                du_ρ'770''45'ki_178 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-d′
d_subst'45'd'8242'_626 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
d_subst'45'd'8242'_626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16
  = case coe v16 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_742 v20 v23 v25 v26 v27
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_742
             (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                   (coe v20))
                (coe v2))
             v23
             (d_subst'45'i'8242'_582
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v10)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v20)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                   (coe v13))
                (coe v14) (coe v15) (coe v25))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v11)
                (coe v20) (coe v26))
             v27
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v22 v23 v24 v25 v26 v27 v32 v33 v34 v35
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v22 v23 v24
             v25 v26 v27 v32 v33
             (coe
                du_ρ'770''45'ki_178 (coe v0) (coe v1) (coe v2) (coe v3) (coe v34))
             v35
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v22 v26
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v27 v28
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v22
                    (d_subst'45'i'8242'_582
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20 (coe v27)
                             (coe v11) (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v11
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v7) (coe v8) (coe v9) (coe v28) (coe v13)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v22 v14)
                       (coe v15) (coe v26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804 v21 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v30 v31
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804
                           (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v21)) v24 v25
                           (d_subst'45'd'8242'_626
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12) (coe v21)
                              (coe v25) (coe v15) (coe v26))
                           (d_subst'45'd'8242'_626
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v31) (coe v21) (coe v12) (coe v13)
                              (coe v24) (coe v15) (coe v27))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v30 v31
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'43'__126 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v24 v25
                                  (d_subst'45'd'8242'_626
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v32) (coe v12)
                                     (coe v13) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_626
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v33) (coe v12)
                                     (coe v13) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v30 v31
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v24 v25
                                  (d_subst'45'd'8242'_626
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v11) (coe v12)
                                     (coe v32) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_626
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12)
                                     (coe v33) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v27
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900
                           (coe
                              du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v27) (coe v23))
                           (d_subst'45'i'8242'_582
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v26)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v27)
                                    (coe v13))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v12))
                                 (coe v13))
                              (coe v14) (coe v15) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
