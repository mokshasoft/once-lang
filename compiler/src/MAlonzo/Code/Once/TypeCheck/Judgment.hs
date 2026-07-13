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
  = C_t'45'int_30 | C_t'45'str_36 | C_t'45'unit_40 |
    C_t'45'unit'45'var_44 |
    C_t'45'var'45'local_56 MAlonzo.Code.Once.Surface.Context.T_SVar_184 |
    C_t'45'var'45'qualified_66 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_174 |
    C_t'45'var'45'resolved_74 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_174 |
    C_t'45'var'45'import_82 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_174 |
    C_t'45'var'45'poly'45'instantiate'45'infer_98 MAlonzo.Code.Once.Type.T_PolyType_244
                                                  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                  T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'annot_108 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'pair_124 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_132 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'let_152 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_182 MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_196 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_210 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_220 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_232 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_244 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_254 MAlonzo.Code.Once.Type.T_Type_112
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_266 MAlonzo.Code.Once.Type.T_Type_112
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_284 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'effApp_300 MAlonzo.Code.Once.Type.T_Type_112
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᵍ_∶_
d__'8866''7501'_'8758'__14 a0 a1 a2 = ()
data T__'8866''7501'_'8758'__14
  = C_g'45'int_306 | C_g'45'terminal_310 |
    C_g'45'pair_322 T__'8866''7501'_'8758'__14
                    T__'8866''7501'_'8758'__14 |
    C_g'45'inl_332 T__'8866''7501'_'8758'__14 |
    C_g'45'inr_342 T__'8866''7501'_'8758'__14 |
    C_g'45'In_352 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188
                  T__'8866''7501'_'8758'__14
-- Once.TypeCheck.Judgment._⊢ᵐ_∶_⇨[_]_
d__'8866''7504'_'8758'_'8680''91'_'93'__18 a0 a1 a2 a3 a4 = ()
data T__'8866''7504'_'8758'_'8680''91'_'93'__18
  = C_m'45'id_360 | C_m'45'fst_370 | C_m'45'snd_380 |
    C_m'45'terminal_388 | C_m'45'initial_396 | C_m'45'inl_406 |
    C_m'45'inr_416 |
    C_m'45'compose_432 MAlonzo.Code.Once.Type.T_Type_112
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'case_448 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'pair_462 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'curry_474 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'cata_488 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'const_500 T__'8866''7501'_'8758'__14 |
    C_m'45'named_512 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148
                     MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_174 |
    C_m'45'named'45'resolved_524 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148
                                 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_174
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__24 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__24
  = C_t'45'morph'45'lift_536 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_t'45'embed_546 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_564 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'value'45'lift_576 T__'8866''7501'_'8758'__14 |
    C_t'45'pair'45'lit'45'check_592 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__24
                                    T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'In'45'app'45'check_604 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188
                                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'apply'45'check_616 MAlonzo.Code.Once.Type.T_Type_112
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_628 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'inr'45'app'45'check_640 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'initial'45'app'45'check_650 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'subsume_662 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'arg'45'driven'45'app'45'check_678 MAlonzo.Code.Once.Type.T_Type_112
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'var'45'poly'45'instantiate_692 MAlonzo.Code.Once.Type.T_PolyType_244
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__698 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__698 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_710 = erased
-- Once.TypeCheck.Judgment.extractMorphWitness
d_extractMorphWitness_732 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_extractMorphWitness_732 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_extractMorphWitness_732 v1 v6
du_extractMorphWitness_732 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_extractMorphWitness_732 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         C_t'45'morph'45'lift_536 v8
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
         C_t'45'embed_546 v7
           -> case coe v7 of
                C_t'45'var'45'resolved_74 v12
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_186 v17 v18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe C_m'45'named'45'resolved_524 v17 v18)
                              _ -> coe v2
                       _ -> coe v2
                C_t'45'var'45'import_82 v14
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
                         -> case coe v14 of
                              MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_186 v19 v20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe C_m'45'named_512 v19 v20)
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         C_t'45'value'45'lift_576 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'const_500 v8)
         _ -> coe v2)
