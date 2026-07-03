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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_30 | C_t'45'str_36 | C_t'45'unit_40 |
    C_t'45'unit'45'var_44 |
    C_t'45'var'45'local_56 MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 |
    C_t'45'var'45'qualified_66 | C_t'45'var'45'resolved_74 |
    C_t'45'var'45'import_82 |
    C_t'45'annot_92 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'pair_108 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_116 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'let_136 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_166 MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_180 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_194 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                            MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_204 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_216 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_228 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_238 MAlonzo.Code.Once.Type.T_Type_112
                               MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_250 MAlonzo.Code.Once.Type.T_Type_112
                                     MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_268 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'effApp_284 MAlonzo.Code.Once.Type.T_Type_112
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᵍ_∶_
d__'8866''7501'_'8758'__14 a0 a1 a2 = ()
data T__'8866''7501'_'8758'__14
  = C_g'45'int_290 | C_g'45'terminal_294 |
    C_g'45'pair_306 T__'8866''7501'_'8758'__14
                    T__'8866''7501'_'8758'__14 |
    C_g'45'inl_316 T__'8866''7501'_'8758'__14 |
    C_g'45'inr_326 T__'8866''7501'_'8758'__14 |
    C_g'45'In_336 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T__'8866''7501'_'8758'__14
-- Once.TypeCheck.Judgment._⊢ᵐ_∶_⇨[_]_
d__'8866''7504'_'8758'_'8680''91'_'93'__18 a0 a1 a2 a3 a4 = ()
data T__'8866''7504'_'8758'_'8680''91'_'93'__18
  = C_m'45'id_344 | C_m'45'fst_354 | C_m'45'snd_364 |
    C_m'45'terminal_372 | C_m'45'initial_380 | C_m'45'inl_390 |
    C_m'45'inr_400 |
    C_m'45'compose_416 MAlonzo.Code.Once.Type.T_Type_112
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'case_432 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'pair_446 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'curry_458 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'cata_472 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'const_484 T__'8866''7501'_'8758'__14 | C_m'45'named_496 |
    C_m'45'named'45'resolved_508
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__24 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__24
  = C_t'45'morph'45'lift_520 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_t'45'embed_530 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_548 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'value'45'lift_560 T__'8866''7501'_'8758'__14 |
    C_t'45'pair'45'lit'45'check_576 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__24
                                    T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'In'45'app'45'check_588 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                  T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'apply'45'check_600 MAlonzo.Code.Once.Type.T_Type_112
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_612 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'inr'45'app'45'check_624 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'initial'45'app'45'check_634 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'subsume_646 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'arg'45'driven'45'app'45'check_662 MAlonzo.Code.Once.Type.T_Type_112
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'var'45'poly'45'instantiate_674 MAlonzo.Code.Once.Type.T_PolyType_244
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__680 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__680 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_692 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d_Typed_692 = erased
-- Once.TypeCheck.Judgment.extractMorphWitness
d_extractMorphWitness_714 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_extractMorphWitness_714 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_extractMorphWitness_714 v1 v6
du_extractMorphWitness_714 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_extractMorphWitness_714 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         C_t'45'morph'45'lift_520 v8
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
         C_t'45'embed_530 v7
           -> case coe v7 of
                C_t'45'var'45'resolved_74
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe C_m'45'named'45'resolved_508)
                       _ -> coe v2
                C_t'45'var'45'import_82
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'named_496)
                       _ -> coe v2
                _ -> coe v2
         C_t'45'value'45'lift_560 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'const_484 v8)
         _ -> coe v2)
