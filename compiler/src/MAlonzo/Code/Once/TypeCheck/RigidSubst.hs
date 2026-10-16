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
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.TypeCheck.RigidSubst.ρ̂
d_ρ'770'_14 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_ρ'770'_14 v0 v1 v2 ~v3 v4 = du_ρ'770'_14 v0 v1 v2 v4
du_ρ'770'_14 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_ρ'770'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
-- Once.TypeCheck.RigidSubst.ρ̂F
d_ρ'770'F_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6
d_ρ'770'F_18 v0 v1 v2 ~v3 v4 = du_ρ'770'F_18 v0 v1 v2 v4
du_ρ'770'F_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6
du_ρ'770'F_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'F_348 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
-- Once.TypeCheck.RigidSubst.ρ̂-⟦⟧
d_ρ'770''45''10214''10215'_26 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45''10214''10215'_26 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-base
d_ρ'770''45'base_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_ρ'770''45'base_36 v0 v1 ~v2 v3 v4 v5
  = du_ρ'770''45'base_36 v0 v1 v3 v4 v5
du_ρ'770''45'base_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
du_ρ'770''45'base_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.du_base'45''10218''10219'_750
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'base_318 (coe v0)
         (coe v1) (coe v3) (coe v4))
-- Once.TypeCheck.RigidSubst.ρ̂-wf
d_ρ'770''45'wf_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
d_ρ'770''45'wf_42 v0 v1 ~v2 v3 v4 v5
  = du_ρ'770''45'wf_42 v0 v1 v3 v4 v5
du_ρ'770''45'wf_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
du_ρ'770''45'wf_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.du_wf'45''10218''10219'_788
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352 (coe v0) (coe v1)
         (coe v3) (coe v4))
-- Once.TypeCheck.RigidSubst.ρ̂-rf
d_ρ'770''45'rf_48 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'rf_48 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-<:
d_ρ'770''45''60''58'_60 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_ρ'770''45''60''58'_60 v0 v1 v2 ~v3 v4 v5 v6
  = du_ρ'770''45''60''58'_60 v0 v1 v2 v4 v5 v6
du_ρ'770''45''60''58'_60 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_ρ'770''45''60''58'_60 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v13 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v19)
                              (coe v16) (coe v13))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v18)
                              (coe v21) (coe v14))
                           v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v9
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v9
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_94
        -> coe
             MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.substPoly-ρ̂
d_substPoly'45'ρ'770'_88 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substPoly'45'ρ'770'_88 = erased
-- Once.TypeCheck.RigidSubst.substPolyF-ρ̂
d_substPolyF'45'ρ'770'_96 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substPolyF'45'ρ'770'_96 = erased
-- Once.TypeCheck.RigidSubst.ρ̂-ki
d_ρ'770''45'ki_188 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ρ'770''45'ki_188 v0 v1 v2 v3 ~v4 ~v5 v6
  = du_ρ'770''45'ki_188 v0 v1 v2 v3 v6
du_ρ'770''45'ki_188 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ρ'770''45'ki_188 v0 v1 v2 v3 v4
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
d_ρ'770'S_204 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6
d_ρ'770'S_204 v0 v1 v2 ~v3 ~v4 v5 = du_ρ'770'S_204 v0 v1 v2 v5
du_ρ'770'S_204 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6
du_ρ'770'S_204 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8 -> coe v3
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
             (coe du_ρ'770'S_204 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v6)) v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.ρ̂N
d_ρ'770'N_212 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8]
d_ρ'770'N_212 v0 v1 v2 ~v3 v4 = du_ρ'770'N_212 v0 v1 v2 v4
du_ρ'770'N_212 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8]
du_ρ'770'N_212 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_name_16 (coe v4))
                (coe
                   du_ρ'770'_14 (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_type_18 (coe v4)))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_quantity_20 (coe v4)))
             (coe du_ρ'770'N_212 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.ρ̂C
d_ρ'770'C_218 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ρ'770'C_218 v0 v1 v2 ~v3 v4 = du_ρ'770'C_218 v0 v1 v2 v4
du_ρ'770'C_218 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ρ'770'C_218 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130 v4 v5 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130 (coe v4)
             (coe du_ρ'770'N_212 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe du_ρ'770'S_204 (coe v0) (coe v1) (coe v2) (coe v6)) (coe v7)
             (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.lookup-ρ̂
d_lookup'45'ρ'770'_238 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'ρ'770'_238 = erased
-- Once.TypeCheck.RigidSubst.lk-just
d_lk'45'just_264 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk'45'just_264 = erased
-- Once.TypeCheck.RigidSubst.lk-nothing
d_lk'45'nothing_386 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk'45'nothing_386 = erased
-- Once.TypeCheck.RigidSubst.ImportsRF
d_ImportsRF_484 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_ImportsRF_484 = erased
-- Once.TypeCheck.RigidSubst.TopRF
d_TopRF_492 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_TopRF_492 = erased
-- Once.TypeCheck.RigidSubst._⇝ᵢ_
d__'8669''7522'__508 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d__'8669''7522'__508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du__'8669''7522'__508 v10
du__'8669''7522'__508 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du__'8669''7522'__508 v0 = coe v0
-- Once.TypeCheck.RigidSubst._⇝ᶜ_
d__'8669''7580'__522 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d__'8669''7580'__522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du__'8669''7580'__522 v10
du__'8669''7580'__522 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du__'8669''7580'__522 v0 = coe v0
-- Once.TypeCheck.RigidSubst.subst-i
d_subst'45'i_534 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_subst'45'i_534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130 v10 v11 v12 v13 v14 v15
        -> coe
             d_subst'45'i'8242'_578 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-c
d_subst'45'c_544 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_subst'45'c_544 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130 v10 v11 v12 v13 v14 v15
        -> coe
             d_subst'45'c'8242'_598 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-d
d_subst'45'd_558 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
d_subst'45'd_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130 v12 v13 v14 v15 v16 v17
        -> coe
             d_subst'45'd'8242'_646 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-i′
d_subst'45'i'8242'_578 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_subst'45'i'8242'_578 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v19
        -> case coe v19 of
             MAlonzo.Code.Once.Lang.Context.C_svar_120 v23
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62
                    (coe MAlonzo.Code.Once.Lang.Context.C_svar_120 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'qualified_72 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'qualified_72 v20
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v18 v20
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v18 v20
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v20
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v21
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v18 v19 v20 v21 v25
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112
             v18 v19 v20 v21 v25
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_122 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_122 v19
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v12) (coe v13)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v20 v21
                           (d_subst'45'i'8242'_578
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v24) (coe v26) (coe v20) (coe v13)
                              (coe v22))
                           (d_subst'45'i'8242'_578
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v25) (coe v27) (coe v21) (coe v13)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_146 v18
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_146
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v20)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v13)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_158
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_158
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_178 v19 v21 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'let_178
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v19)) v21 v22 v23
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v27) (coe v19) (coe v22) (coe v13)
                       (coe v24))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22 (coe v26)
                             (coe v19) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v6 v19
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe v7) (coe v8) (coe v9) (coe v28) (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v21 v23)
                       (coe v13) (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_208 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v32 v33 v34 v35 v36
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'case_208
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v21))
                       (coe v2))
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v22))
                       (coe v2))
                    v24 v25 v26 v27 v28
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v32)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v21) (coe v22))
                       (coe v26) (coe v13) (coe v29))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22 (coe v33)
                             (coe v21) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v6 v21
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe v7) (coe v8) (coe v9) (coe v34) (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v24 v27)
                       (coe v13) (coe v30))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22 (coe v35)
                             (coe v22) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v6 v22
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe v7) (coe v8) (coe v9) (coe v36) (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v25 v28)
                       (coe v13) (coe v31))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v19 v20
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_236 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_236
                    v19 v20
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_250 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_250
                    v19 v20
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_264 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_264
                    v19 v20
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v19 v20
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v19) (coe v13)
                       (coe v22))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v20) (coe v13)
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_288 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_288 v18
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_300 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_300
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v18))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v11) (coe v18))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_312 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_312
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v17) (coe v11))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_322 v17 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_322
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17)) v18
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v17) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350 v17 v19 v21 v22
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v25 v26 v27
                      -> case coe v26 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v28 v29
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350
                                  (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                                     (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0)
                                        (coe v1) (coe v17))
                                     (coe v2))
                                  v19 v21
                                  (d_subst'45'i'8242'_578
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v24)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v17)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v29))
                                           (coe v27))
                                        (coe v17))
                                     (coe v19) (coe v13) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362 v17 v19 v20 v22
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362
                    (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19
                    (coe
                       du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17) (coe v20))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v17)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                       (coe v19) (coe v13) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378 v17 v19 v21 v22 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                      -> case coe v28 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v30 v31
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378
                                  (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19 v21
                                  (coe
                                     du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17)
                                     (coe v22))
                                  (d_subst'45'i'8242'_578
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v26)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v17)
                                        (coe v31))
                                     (coe v19) (coe v13) (coe v24))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396 v18 v20 v21 v22 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v18))
                       (coe v2))
                    v20 v21 v22
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v18)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v20)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v11))
                       (coe v21) (coe v13) (coe v24))
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v27) (coe v18) (coe v22) (coe v13)
                       (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v18 v20 v21 v23 v25 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v27 v28
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v29 v30 v31
                      -> case coe v30 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416
                                  (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                                     (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0)
                                        (coe v1) (coe v18))
                                     (coe v2))
                                  v20 v21 v23
                                  (d_subst'45'i'8242'_578
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v27)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v18)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v33))
                                        (coe v31))
                                     (coe v20) (coe v13) (coe v25))
                                  (d_subst'45'c'8242'_598
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v28) (coe v18) (coe v21)
                                     (coe v13) (coe v26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432 v18 v20 v21 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v18)) v20 v21
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26) (coe v18) (coe v21) (coe v13)
                       (coe v23))
                    (d_subst'45'd'8242'_646
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v25) (coe v18)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v11)
                       (coe v20) (coe v13) (coe v24))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-c′
d_subst'45'c'8242'_598 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_subst'45'c'8242'_598 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_442 v18
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_442 v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_454 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_454 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_466 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_466 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_476 v18
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_476
             v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_486 v18
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_486
             v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_498 v19
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_498 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_510 v19
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_510 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_530 v19 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v33 v34
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_530
                                         (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v19)) v22
                                         v23
                                         (d_subst'45'd'8242'_646
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v27) (coe v30)
                                            (coe v34) (coe v19) (coe v23) (coe v13) (coe v24))
                                         (d_subst'45'c'8242'_598
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v29)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v34))
                                               (coe v32))
                                            (coe v22) (coe v13) (coe v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_554 v19 v21 v23 v24 v25 v26 v27 v28
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v29 v30
               -> case coe v29 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v31 v32
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v33 v34 v35
                             -> case coe v34 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v36 v37
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_554
                                         (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0)
                                               (coe v1) (coe v19))
                                            (coe v2))
                                         (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0)
                                               (coe v1) (coe v21))
                                            (coe v2))
                                         v23 v24 v25
                                         (d_subst'45'i'8242'_578
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v32)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v23))
                                               (coe v21))
                                            (coe v24) (coe v13) (coe v26))
                                         (coe
                                            du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v23))
                                               (coe v21))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v37))
                                               (coe v35))
                                            (coe v27))
                                         (d_subst'45'c'8242'_598
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v30)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v33)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v37))
                                               (coe v19))
                                            (coe v25) (coe v13) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_574 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v30 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v33 v34
                                    -> case coe v31 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_574
                                                v22 v23
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v33)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v36))
                                                      (coe v32))
                                                   (coe v22) (coe v13) (coe v24))
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v27)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v34)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v36))
                                                      (coe v32))
                                                   (coe v23) (coe v13) (coe v25))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_594 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v33 v34
                                    -> case coe v32 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_594
                                                v22 v23
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v34))
                                                      (coe v35))
                                                   (coe v22) (coe v13) (coe v24))
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v27)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v34))
                                                      (coe v36))
                                                   (coe v23) (coe v13) (coe v25))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_614 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                      -> case coe v29 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v33 v34
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_614 v23
                                         (d_subst'45'c'8242'_598
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v26)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v27)
                                                  (coe v30))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v34))
                                               (coe v32))
                                            (coe v12) (coe v13) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_630 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v26 v27 v28
                      -> case coe v26 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v29
                             -> case coe v27 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v30 v31
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_630 v20
                                         v21
                                         (coe
                                            du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v29)
                                            (coe v22))
                                         (d_subst'45'c'8242'_598
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v25)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                  (coe v29) (coe v28))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v31))
                                               (coe v28))
                                            (coe v20) (coe v13) (coe v23))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_648 v21 v22 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                      -> case coe v29 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v30 v31
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_648 v21 v22
                                  (coe
                                     du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v30)
                                     (coe v23))
                                  (d_subst'45'c'8242'_598
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v26)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v27)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v31))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v30) (coe v27)))
                                     (coe v21) (coe v13) (coe v24))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v17 v20 v21
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17))
             (d_subst'45'i'8242'_578
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v10) (coe v17) (coe v12) (coe v13)
                (coe v20))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v17)
                (coe v11) (coe v21))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved'45'guard_674 v20 v21 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v26 v27 v28
                      -> case coe v27 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v29 v30
                             -> coe
                                  du_guard'45'rf_622 (coe v20)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v13
                                     (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v25))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v26)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe v29) (coe v20))
                                        (coe v28))
                                     erased)
                                  (coe v21) (coe v23) (coe v24)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_696 v21 v24 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v27 v28
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v29 v30 v31
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_696 v21 v24
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe addInt (coe (1 :: Integer)) (coe v4))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22 (coe v27)
                                    (coe v29) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                 (coe v5))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v6 v29
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                              (coe v7) (coe v8) (coe v9) (coe v28) (coe v31)
                              (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v21 v12)
                              (coe v13) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_712 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_712 v20
                           v21
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v24) (coe v26) (coe v20) (coe v13)
                              (coe v22))
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v25) (coe v27) (coe v21) (coe v13)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_722 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v23
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_722 v18
                           (coe
                              du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v23) (coe v19))
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v23)
                                 (coe v11))
                              (coe v18) (coe v13) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_734 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_734
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v17))
                       (coe v2))
                    v19
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_746 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_746 v19
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v23) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_758 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_758 v19
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v24) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_768 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_768
                    v18
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_782 v18 v19 v20 v25
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_782
             v18 v19 v20
             (coe
                du_ρ'770''45'ki_188 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.guard-rf
d_guard'45'rf_622 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_guard'45'rf_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 v14 v15 v16 ~v17 v18 v19
  = du_guard'45'rf_622 v14 v15 v16 v18 v19
du_guard'45'rf_622 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_guard'45'rf_622 v0 v1 v2 v3 v4
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved'45'guard_674
         v0 v2 v3 v4)
-- Once.TypeCheck.RigidSubst.subst-d′
d_subst'45'd'8242'_646 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Lang.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
d_subst'45'd'8242'_646 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16
  = case coe v16 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_800 v20 v23 v25 v26 v27
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_800
             (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                   (coe v20))
                (coe v2))
             v23
             (d_subst'45'i'8242'_578
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v10)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23))
                   (coe v13))
                (coe v14) (coe v15) (coe v25))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v11)
                (coe v20) (coe v26))
             v27
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v22 v23 v24 v25 v26 v27 v32 v33 v34 v35
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v22 v23 v24 v25 v26
             v27 v32 v33
             (coe
                du_ρ'770''45'ki_188 (coe v0) (coe v1) (coe v2) (coe v3) (coe v34))
             v35
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v22 v25 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v27 v28
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v22 v25
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22 (coe v27)
                             (coe v11) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v6 v11
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe v7) (coe v8) (coe v9) (coe v28) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v22 v14)
                       (coe v15) (coe v26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v21 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864
                           (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v21)) v24 v25
                           (d_subst'45'd'8242'_646
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12) (coe v21)
                              (coe v25) (coe v15) (coe v26))
                           (d_subst'45'd'8242'_646
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v31) (coe v21) (coe v12) (coe v13)
                              (coe v24) (coe v15) (coe v27))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v20
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v21
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v21
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v20
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v19
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v24 v25
                                  (d_subst'45'd'8242'_646
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v32) (coe v12)
                                     (coe v13) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_646
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v33) (coe v12)
                                     (coe v13) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> case coe v13 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v24 v25
                                  (d_subst'45'd'8242'_646
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v11) (coe v12)
                                     (coe v32) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_646
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12)
                                     (coe v33) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v28
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v22 v23
                           (coe
                              du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v28) (coe v24))
                           (d_subst'45'i'8242'_578
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v27)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v28)
                                    (coe v13))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v12))
                                 (coe v13))
                              (coe v22) (coe v15) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
