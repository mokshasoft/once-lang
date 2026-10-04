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

module MAlonzo.Code.Once.Spec.Core.Meaning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.GradedOps
import qualified MAlonzo.Code.Once.Denotation.PhaseV
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.Word

-- Once.Spec.Core.Meaning._.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Spec.Core.Meaning._.primCod
d_primCod_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primCod_100 ~v0 ~v1 ~v2 = du_primCod_100
du_primCod_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primCod_100
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Spec.Core.Meaning._.primDom
d_primDom_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primDom_102 ~v0 ~v1 ~v2 = du_primDom_102
du_primDom_102 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primDom_102
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Spec.Core.Meaning._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Core.Meaning.DefSem
d_DefSem_340 a0 a1 a2 = ()
data T_DefSem_340
  = C_defSem_358 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                   MAlonzo.Code.Once.Type.T_Type_108) ->
                  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
                  AgdaAny)
                 MAlonzo.Code.Once.Spec.Contract.T_Impl_408
-- Once.Spec.Core.Meaning.DefSem.defs
d_defs_354 ::
  T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  AgdaAny
d_defs_354 v0
  = case coe v0 of
      C_defSem_358 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Meaning.DefSem.impl
d_impl_356 ::
  T_DefSem_340 -> MAlonzo.Code.Once.Spec.Contract.T_Impl_408
d_impl_356 v0
  = case coe v0 of
      C_defSem_358 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Meaning.Env
d_Env_362 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Env_362 = erased
-- Once.Spec.Core.Meaning.primSem
d_primSem_370 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny -> AgdaAny
d_primSem_370 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'add_22
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_298
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'sub_24
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_300
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'mul_26
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_302
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'div_28
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_304
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'mod_30
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_306
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'neg_32
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_308
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'lt_34
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_322
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'le_36
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_324
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'gt_38
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_326
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'ge_40
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_328
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'eq_42
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_330
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'ne_44
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_332
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'pure_368) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fadd_46
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_312
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fsub_48
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_314
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fmul_50
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_316
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fdiv_52
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_318
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'i2f_54
        -> coe
             MAlonzo.Code.Once.SigOp.Info.du_semP_418
             MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_320
             (coe MAlonzo.Code.Once.SigOp.Info.C_int'45'prim_372) v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Meaning.⟦_⟧
d_'10214'_'10215'_452 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_DefSem_340 -> AgdaAny -> AgdaAny
d_'10214'_'10215'_452 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9
  = du_'10214'_'10215'_452 v0 v4 v6 v7 v8 v9
du_'10214'_'10215'_452 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_DefSem_340 -> AgdaAny -> AgdaAny
du_'10214'_'10215'_452 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66 v9
               -> coe
                    (\ v10 v11 v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.PhaseV.du_lookup'7515'Used_12 (coe v1)
                         (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v10 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         seq (coe v10)
                                         (coe
                                            (\ v23 v24 v25 v26 ->
                                               coe
                                                 du_'10214'_'10215'_452 v0
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                    (coe v1) (coe v18))
                                                 v17 v20 v22 v16 v23 v24 v25))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Type.C_Zero_6
                                           -> coe
                                                (\ v23 v24 v25 v26 ->
                                                   coe
                                                     du_'10214'_'10215'_452 v0
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v18))
                                                     v17 v20 v22 v16 v23 v24 v25)
                                         MAlonzo.Code.Once.Type.C_One_8
                                           -> coe
                                                (\ v23 v24 v25 v26 ->
                                                   coe
                                                     du_'10214'_'10215'_452 v0
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v18))
                                                     v17 v20 v22 v16 v23 v24
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114
                                                        (coe v10) (coe v25) (coe v26)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Type.C_Zero_6
                                           -> coe
                                                (\ v23 v24 v25 v26 ->
                                                   coe
                                                     du_'10214'_'10215'_452 v0
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v18))
                                                     v17 v20 v22 v16 v23 v24 v25)
                                         MAlonzo.Code.Once.Type.C_One_8
                                           -> coe
                                                (\ v23 v24 v25 v26 ->
                                                   coe
                                                     du_'10214'_'10215'_452 v0
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v18))
                                                     v17 v20 v22 v16 v23 v24
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114
                                                        (coe v10) (coe v25) (coe v26)))
                                         MAlonzo.Code.Once.Type.C_Many_10
                                           -> coe
                                                (\ v23 v24 v25 v26 ->
                                                   coe
                                                     du_'10214'_'10215'_452 v0
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v18))
                                                     v17 v20 v22 v16 v23 v24
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114
                                                        (coe v10) (coe v25) (coe v26)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v8 v9 v10 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 v18 v19
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v18
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10) (coe v4))
                                      (coe v3))
                                   v4 v16 v20 v21
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v22)))
                                (coe
                                   (\ v23 -> coe v23 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v18
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10) (coe v4))
                                      (coe v3))
                                   v4 v16 v20 v21
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v22)))
                                (coe
                                   MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                   (coe
                                      du_'10214'_'10215'_452 v0 v1 v19 v12 v4 v17 v20 v21
                                      (coe
                                         MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v8)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v9)))
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v9))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe v10) (coe v9)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                               (coe v9))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe v10) (coe v9))))
                                         (coe v22)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v18
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10) (coe v4))
                                      (coe v3))
                                   v4 v16 v20 v21
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v9)))
                                      (coe v22)))
                                (coe
                                   MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                   (coe
                                      du_'10214'_'10215'_452 v0 v1 v19 v12 v4 v17 v20 v21
                                      (coe
                                         MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v8)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v9)))
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v9))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe v10) (coe v9)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                               (coe v9))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe v10) (coe v9))))
                                         (coe v22)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v8 v9 v10 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 v18 v19
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                du_'10214'_'10215'_452 v0
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                   (coe v12))
                                v19 v3 v4 v17 v20 v21
                                (coe
                                   MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v10) (coe v8)))
                                   (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v10) (coe v8)))
                                   (coe v22)))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v18 v12 v4 v16 v20 v21
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v8)))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v8)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                            (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v8))))
                                      (coe v22)))
                                (coe
                                   (\ v23 ->
                                      coe
                                        du_'10214'_'10215'_452 v0
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                           (coe v12))
                                        v19 v3 v4 v17 v20 v21
                                        (coe
                                           MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                    (coe v10) (coe v8)))
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                    (coe v10) (coe v8)))
                                              (coe v22))
                                           (coe v23)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v20 v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v18 v12 v4 v16 v20 v21
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v8)))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                            (coe v10) (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v8)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                            (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe v10) (coe v8))))
                                      (coe v22)))
                                (coe
                                   (\ v23 ->
                                      coe
                                        du_'10214'_'10215'_452 v0
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                           (coe v12))
                                        v19 v3 v4 v17 v20 v21
                                        (coe
                                           MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                    (coe v10) (coe v8)))
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                    (coe v10) (coe v8)))
                                              (coe v22))
                                           (coe v23)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
        -> coe (\ v8 v9 v10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v8 v9 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v19 v20
                      -> coe
                           (\ v21 v22 v23 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v17 v19 v4 v15 v21 v22
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v8) (coe v9))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                         (coe v8) (coe v9))
                                      (coe v23)))
                                (coe
                                   (\ v24 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74
                                        (coe v4)
                                        (coe
                                           du_'10214'_'10215'_452 v0 v1 v18 v20 v4 v16 v21 v22
                                           (coe
                                              MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                 (coe v8) (coe v9))
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                                 (coe v8) (coe v9))
                                              (coe v23)))
                                        (coe
                                           (\ v25 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v24) (coe v25)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78 v14
               -> coe
                    (\ v15 v16 v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v14
                            (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v3) (coe v11)) v4 v13
                            v15 v16 v17)
                         (coe
                            (\ v18 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102 (coe v4)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v10 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80 v14
               -> coe
                    (\ v15 v16 v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v14
                            (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v10) (coe v3)) v4 v13
                            v15 v16 v17)
                         (coe
                            (\ v18 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102 (coe v4)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v15 v16
                      -> coe
                           (\ v17 v18 v19 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe du_'10214'_'10215'_452 v0 v1 v14 v15 v4 v13 v17 v18 v19)
                                (coe
                                   (\ v20 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102
                                        (coe v4)
                                        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v20)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v15 v16
                      -> coe
                           (\ v17 v18 v19 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe du_'10214'_'10215'_452 v0 v1 v14 v16 v4 v13 v17 v18 v19)
                                (coe
                                   (\ v20 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102
                                        (coe v4)
                                        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v20)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_436 v8 v9 v10 v11 v12 v14 v15 v20 v21 v22
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 v23 v24 v25
               -> coe
                    (\ v26 v27 v28 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v23
                            (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v14) (coe v15)) v4
                            v20 v26 v27
                            (coe
                               MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                     (coe v9) (coe v10)))
                               (coe v8)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                  (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                     (coe v9) (coe v10)))
                               (coe v28)))
                         (coe
                            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                            (\ v29 ->
                               coe
                                 du_'10214'_'10215'_452 v0
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                    (coe v14))
                                 v24 v3 v4 v21 v26 v27
                                 (coe
                                    MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                          (coe v9) (coe v10))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
                                          (coe v9) (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                          (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                             (coe v8)
                                             (coe
                                                MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                (coe v9) (coe v10)))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                             (coe v9) (coe v10))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                             (coe v8)
                                             (coe
                                                MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                (coe v9) (coe v10)))
                                          (coe v28)))
                                    (coe v29)))
                            (\ v29 ->
                               coe
                                 du_'10214'_'10215'_452 v0
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                    (coe v15))
                                 v25 v3 v4 v22 v26 v27
                                 (coe
                                    MAlonzo.Code.Once.Denotation.PhaseV.du_bind'7515'_114 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                          (coe v9) (coe v10))
                                       (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
                                          (coe v9) (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                          (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                             (coe v8)
                                             (coe
                                                MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                (coe v9) (coe v10)))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                             (coe v9) (coe v10))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                             (coe v8)
                                             (coe
                                                MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                (coe v9) (coe v10)))
                                          (coe v28)))
                                    (coe v29)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_450 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88 v13
               -> coe
                    (\ v14 v15 v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v13
                            (coe MAlonzo.Code.Once.Type.C_Void_122) v4 v12 v14 v15 v16)
                         (\ v17 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_464 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v15
                      -> coe
                           (\ v16 v17 v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v14
                                   (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                      (coe v15) (coe v3))
                                   v4 v13 v16 v17 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.GradedOps.d_in'45'value'7515'_220
                                           (coe v15) (coe v12) (coe v19)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_484 v8 v9 v11 v15 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92 v18 v19
               -> coe
                    (\ v20 v21 v22 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v18
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v11) (coe v3))
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                               (coe v3))
                            v4 v16 v20 v21
                            (coe
                               MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                  (coe v9))
                               (coe v8)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                  (coe v8) (coe v9))
                               (coe v22)))
                         (coe
                            (\ v23 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                 (coe
                                    du_'10214'_'10215'_452 v0 v1 v19
                                    (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v11)) v4 v17
                                    v20 v21
                                    (coe
                                       MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                          (coe v8) (coe v9))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                          (coe v8) (coe v9))
                                       (coe v22)))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.GradedOps.du_cata'45'sem'7515'_234
                                    (coe v4) (coe v11) (coe v15) (coe v23)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_506 v8 v9 v13 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94 v19 v20
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v21 v22
                      -> coe
                           (\ v23 v24 v25 ->
                              coe
                                MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                                (coe
                                   du_'10214'_'10215'_452 v0 v1 v20 v13 v4 v18 v23 v24
                                   (coe
                                      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                         (coe v8) (coe v9))
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                         (coe v8) (coe v9))
                                      (coe v25)))
                                (coe
                                   MAlonzo.Code.Once.Denotation.GradedOps.du_ana'45'sem'7515'_374
                                   (coe v21) (coe v22) (coe v4) (coe v16)
                                   (coe
                                      du_'10214'_'10215'_452 v0 v1 v19
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                         (coe
                                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v21)
                                            (coe v13)))
                                      v4 v17 v23 v24
                                      (coe
                                         MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v8) (coe v9))
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                            (coe v8) (coe v9))
                                         (coe v25)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_520 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96 v14
               -> coe
                    (\ v15 v16 v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v14
                            (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v10) (coe v4)) v4
                            v13 v15 v16 v17)
                         (coe
                            MAlonzo.Code.Once.Denotation.GradedOps.d_out'45'sem'7515'_414
                            (coe v4) (coe v10) (coe v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_536 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 v15 v16 v17
               -> coe
                    (\ v18 v19 v20 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedOps.du_fmapM_12 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Denotation.GradedOps.d_'10214'_'10215''60''58''7515'_434
                            (coe v15) (coe v3) (coe v13))
                         (coe du_'10214'_'10215'_452 v0 v1 v17 v15 v4 v14 v18 v19 v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_544
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Core.Syntax.C_lit'45'int_16 v10
                      -> coe
                           (\ v11 v12 v13 ->
                              MAlonzo.Code.Once.Word.d_fromℤ_20
                                (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v11))
                                (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_552
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Core.Syntax.C_lit'45'float_18 v10
                      -> coe
                           (\ v11 v12 v13 ->
                              MAlonzo.Code.Once.Float.Decimal.d_round_174
                                (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v11))
                                (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_566 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 v13 v14
               -> coe
                    (\ v15 v16 v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v4)
                         (coe
                            du_'10214'_'10215'_452 v0 v1 v14
                            (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v13)) v4
                            v12 v15 v16 v17)
                         (coe
                            (\ v18 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102 (coe v4)
                                 (coe d_primSem_370 (coe v13) (coe v15) (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_578 v10 v11 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_sigop_104 v14 v15
               -> coe
                    (\ v16 v17 v18 ->
                       coe
                         MAlonzo.Code.Once.Denotation.GradedOps.du_sigOpRef'7515'_514
                         (coe v3) (coe v16) (coe v0) (coe d_impl_356 (coe v17)) (coe v14)
                         (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_588 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 v11 v12
               -> coe (\ v13 v14 v15 -> coe d_defs_354 v14 v11 v12 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_604 v9 v13 v14
        -> coe
             (\ v15 v16 v17 ->
                coe
                  MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_90 (coe v13)
                  (coe du_'10214'_'10215'_452 v0 v1 v2 v3 v9 v14 v15 v16 v17))
      _ -> MAlonzo.RTE.mazUnreachableError
