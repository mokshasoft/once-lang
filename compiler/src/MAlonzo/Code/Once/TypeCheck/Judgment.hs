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

module MAlonzo.Code.Once.TypeCheck.Judgment where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_30 | C_t'45'float_42 | C_t'45'str_48 |
    C_t'45'unit_52 | C_t'45'unit'45'var_56 |
    C_t'45'var'45'local_68 MAlonzo.Code.Once.Surface.Context.T_SVar_184 |
    C_t'45'var'45'qualified_78 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'resolved_86 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'import_94 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'poly'45'instantiate'45'infer_110 MAlonzo.Code.Once.Type.T_PolyType_244
                                                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'annot_120 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'pair_136 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_144 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_156 |
    C_t'45'let_176 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_206 MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_220 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_234 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_248 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_262 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_276 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_286 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_298 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_310 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_320 MAlonzo.Code.Once.Type.T_Type_112
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_332 MAlonzo.Code.Once.Type.T_Type_112
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_350 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'effApp_366 MAlonzo.Code.Once.Type.T_Type_112
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᵍ_∶_
d__'8866''7501'_'8758'__14 a0 a1 a2 = ()
data T__'8866''7501'_'8758'__14
  = C_g'45'int_372 | C_g'45'float_384 | C_g'45'neg'45'int_390 |
    C_g'45'neg'45'float_402 | C_g'45'terminal_406 |
    C_g'45'pair_418 T__'8866''7501'_'8758'__14
                    T__'8866''7501'_'8758'__14 |
    C_g'45'inl_428 T__'8866''7501'_'8758'__14 |
    C_g'45'inr_438 T__'8866''7501'_'8758'__14 |
    C_g'45'In_448 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                  T__'8866''7501'_'8758'__14
-- Once.TypeCheck.Judgment._⊢ᵐ_∶_⇨[_]_
d__'8866''7504'_'8758'_'8680''91'_'93'__18 a0 a1 a2 a3 a4 = ()
data T__'8866''7504'_'8758'_'8680''91'_'93'__18
  = C_m'45'id_456 | C_m'45'fst_466 | C_m'45'snd_476 |
    C_m'45'terminal_484 | C_m'45'initial_492 | C_m'45'inl_502 |
    C_m'45'inr_512 |
    C_m'45'compose_528 MAlonzo.Code.Once.Type.T_Type_112
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'case_544 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'pair_558 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'curry_570 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'cata_584 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'const_596 T__'8866''7501'_'8758'__14 |
    C_m'45'named_608 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
                     MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_m'45'named'45'resolved_620 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
                                 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__24 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__24
  = C_t'45'morph'45'lift_632 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_t'45'embed_642 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_660 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'value'45'lift_672 T__'8866''7501'_'8758'__14 |
    C_t'45'pair'45'lit'45'check_688 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__24
                                    T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'In'45'app'45'check_700 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'apply'45'check_712 MAlonzo.Code.Once.Type.T_Type_112
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_724 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'inr'45'app'45'check_736 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'initial'45'app'45'check_746 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'subsume_758 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'arg'45'driven'45'app'45'check_774 MAlonzo.Code.Once.Type.T_Type_112
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'var'45'poly'45'instantiate_788 MAlonzo.Code.Once.Type.T_PolyType_244
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__794 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_806 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_806 = erased
-- Once.TypeCheck.Judgment.extractMorphWitness
d_extractMorphWitness_828 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_extractMorphWitness_828 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_extractMorphWitness_828 v1 v6
du_extractMorphWitness_828 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_extractMorphWitness_828 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         C_t'45'morph'45'lift_632 v8
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
         C_t'45'embed_642 v7
           -> case coe v7 of
                C_t'45'var'45'resolved_86 v12
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v17 v18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe C_m'45'named'45'resolved_620 v17 v18)
                              _ -> coe v2
                       _ -> coe v2
                C_t'45'var'45'import_94 v14
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
                         -> case coe v14 of
                              MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v19 v20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe C_m'45'named_608 v19 v20)
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         C_t'45'value'45'lift_672 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'const_596 v8)
         _ -> coe v2)
