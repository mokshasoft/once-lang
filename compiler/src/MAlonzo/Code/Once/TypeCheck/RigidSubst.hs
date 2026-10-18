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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope

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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
du_ρ'770''45''60''58'_60 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36 -> coe v5
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v19)
                              (coe v16) (coe v13))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v18)
                              (coe v21) (coe v14))
                           v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v12)
                              (coe v14) (coe v10))
                           (coe
                              du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_76
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_76
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v9
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v9
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_90
        -> coe
             MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
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
             d_subst'45'd'8242'_622 (coe v0) (coe v1) (coe v2) (coe v3)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v18 v20
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v18 v20
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78 v20
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v21
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102 v18 v19 v20 v21 v25
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102
             v18 v19 v20 v21 v25
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v19
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v12) (coe v13)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v20 v21
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136 v18
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v20)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v13)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168 v19 v21 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_198 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v32 v33 v34 v35 v36
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'case_198
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_212 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_212 v19 v20
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_226 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_226
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_240 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_240
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_254 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_254
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_268 v19 v20 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_268 v19 v20
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_278 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_278 v18
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v11) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_290 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_290
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_302 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_302
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_312 v17 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_312
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17)) v18
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21) (coe v17) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_324 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_324
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
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_340 v17 v19 v21 v22
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v25 v26 v27
                      -> case coe v26 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v28 v29
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_340
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
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v29))
                                           (coe v27))
                                        (coe v17))
                                     (coe v19) (coe v13) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_352 v17 v19 v20 v22
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_352
                    (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19
                    (coe
                       du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17) (coe v20))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v17)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                       (coe v19) (coe v13) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_364 v17 v19 v20 v22
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_364
                    (coe du_ρ'770'F_18 (coe v0) (coe v1) (coe v2) (coe v17)) v19
                    (coe
                       du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v17) (coe v20))
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v17)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                       (coe v19) (coe v13) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_382 v18 v20 v21 v22 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app_382
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
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v20)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v11))
                       (coe v21) (coe v13) (coe v24))
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v27) (coe v18) (coe v22) (coe v13)
                       (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_402 v18 v20 v21 v23 v25 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v27 v28
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v29 v30 v31
                      -> case coe v30 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_402
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
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_418 v18 v20 v21 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_418
                    (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v18)) v20 v21
                    (d_subst'45'i'8242'_578
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v26) (coe v18) (coe v21) (coe v13)
                       (coe v23))
                    (d_subst'45'd'8242'_622
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_428 v18
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_428 v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_440 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_440 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_452 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_452 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_462 v18
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_462
             v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_472 v18
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_472
             v18
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_484 v19
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_484 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_496 v19
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_496 v19
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_516 v19 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v33 v34
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_516
                                         (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v19)) v22
                                         v23
                                         (d_subst'45'd'8242'_622
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
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v34))
                                               (coe v32))
                                            (coe v22) (coe v13) (coe v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_540 v19 v21 v23 v24 v25 v26 v27 v28
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v29 v30
               -> case coe v29 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v31 v32
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v33 v34 v35
                             -> case coe v34 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v36 v37
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_540
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
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v23))
                                               (coe v21))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v37))
                                               (coe v19))
                                            (coe v25) (coe v13) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_560 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v30 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v33 v34
                                    -> case coe v31 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_560
                                                v22 v23
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v33)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_580 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v33 v34
                                    -> case coe v32 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v35 v36
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_580
                                                v22 v23
                                                (d_subst'45'c'8242'_598
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_600 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                      -> case coe v29 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v30 v31 v32
                             -> case coe v31 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v33 v34
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_600 v23
                                         (d_subst'45'c'8242'_598
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v26)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v27)
                                                  (coe v30))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v34))
                                               (coe v32))
                                            (coe v12) (coe v13) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_616 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v26 v27 v28
                      -> case coe v26 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v29
                             -> case coe v27 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v30 v31
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_616 v20
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
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v31))
                                               (coe v28))
                                            (coe v20) (coe v13) (coe v23))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_634 v21 v22 v23 v24
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                      -> case coe v29 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v30 v31
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_634 v21 v22
                                  (coe
                                     du_ρ'770''45'wf_42 (coe v0) (coe v1) (coe v3) (coe v30)
                                     (coe v23))
                                  (d_subst'45'c'8242'_598
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v26)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v27)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v31)))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v30) (coe v27)))
                                     (coe v21) (coe v13) (coe v24))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_646 v17 v20 v21
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_646
             (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v17))
             (d_subst'45'i'8242'_578
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v10) (coe v17) (coe v12) (coe v13)
                (coe v20))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v17)
                (coe v11) (coe v21))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_668 v21 v24 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v27 v28
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v29 v30 v31
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_668 v21 v24
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_684 v20 v21 v22 v23
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v24 v25
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_684 v20
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_694 v18 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v23
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_694 v18
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_706 v17 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_706
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
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v11))
                          (coe v17))
                       (coe v19) (coe v13) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_718 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_718 v19
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v23) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_730 v19 v20
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_730 v19
                           (d_subst'45'c'8242'_598
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v22) (coe v24) (coe v19) (coe v13)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_740 v18 v19
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_740
                    v18
                    (d_subst'45'c'8242'_598
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v21)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v18) (coe v13)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_754 v18 v19 v20 v25
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_754
             v18 v19 v20
             (coe
                du_ρ'770''45'ki_188 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.RigidSubst.subst-d′
d_subst'45'd'8242'_622 ::
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
d_subst'45'd'8242'_622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16
  = case coe v16 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_772 v20 v23 v25 v26 v27
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_772
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
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23))
                   (coe v13))
                (coe v14) (coe v15) (coe v25))
             (coe
                du_ρ'770''45''60''58'_60 (coe v0) (coe v1) (coe v2) (coe v11)
                (coe v20) (coe v26))
             v27
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_796 v22 v23 v24 v25 v26 v27 v32 v33 v34 v35
        -> coe
             MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_796 v22 v23 v24 v25 v26
             v27 v32 v33
             (coe
                du_ρ'770''45'ki_188 (coe v0) (coe v1) (coe v2) (coe v3) (coe v34))
             v35
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_816 v22 v25 v26
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v27 v28
               -> coe
                    MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_816 v22 v25
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_836 v21 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_836
                           (coe du_ρ'770'_14 (coe v0) (coe v1) (coe v2) (coe v21)) v24 v25
                           (d_subst'45'd'8242'_622
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12) (coe v21)
                              (coe v25) (coe v15) (coe v26))
                           (d_subst'45'd'8242'_622
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v31) (coe v21) (coe v12) (coe v13)
                              (coe v24) (coe v15) (coe v27))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_846 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'id_846 v20
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_858 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_858 v21
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_870 v21
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_870 v21
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_880 v20
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_880 v20
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_888 v19
        -> coe MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_888 v19
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_908 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_d'45'case_908 v24 v25
                                  (d_subst'45'd'8242'_622
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v32) (coe v12)
                                     (coe v13) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_622
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v33) (coe v12)
                                     (coe v13) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_928 v24 v25 v26 v27
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v28 v29
               -> case coe v28 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v30 v31
                      -> case coe v13 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v32 v33
                             -> coe
                                  MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_928 v24 v25
                                  (d_subst'45'd'8242'_622
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v31) (coe v11) (coe v12)
                                     (coe v32) (coe v24) (coe v15) (coe v26))
                                  (d_subst'45'd'8242'_622
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                     (coe v7) (coe v8) (coe v9) (coe v29) (coe v11) (coe v12)
                                     (coe v33) (coe v25) (coe v15) (coe v27))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_944 v22 v23 v24 v25
        -> case coe v10 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v26 v27
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v28
                      -> coe
                           MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_944 v22 v23
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
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v12))
                                 (coe v13))
                              (coe v22) (coe v15) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
