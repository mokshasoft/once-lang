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
    C_t'45'arr'45'app'45'infer_250 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_262 MAlonzo.Code.Once.Type.T_Type_112
                                     MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_280 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'effApp_296 MAlonzo.Code.Once.Type.T_Type_112
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᵍ_∶_
d__'8866''7501'_'8758'__14 a0 a1 a2 = ()
data T__'8866''7501'_'8758'__14
  = C_g'45'int_302 | C_g'45'terminal_306 |
    C_g'45'pair_318 T__'8866''7501'_'8758'__14
                    T__'8866''7501'_'8758'__14 |
    C_g'45'inl_328 T__'8866''7501'_'8758'__14 |
    C_g'45'inr_338 T__'8866''7501'_'8758'__14 |
    C_g'45'In_348 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T__'8866''7501'_'8758'__14
-- Once.TypeCheck.Judgment._⊢ᵐ_∶_⇨[_]_
d__'8866''7504'_'8758'_'8680''91'_'93'__18 a0 a1 a2 a3 a4 = ()
data T__'8866''7504'_'8758'_'8680''91'_'93'__18
  = C_m'45'id_356 | C_m'45'fst_366 | C_m'45'snd_376 |
    C_m'45'terminal_384 | C_m'45'initial_392 | C_m'45'inl_402 |
    C_m'45'inr_412 |
    C_m'45'compose_428 MAlonzo.Code.Once.Type.T_Type_112
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18
                       T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'case_444 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'pair_458 T__'8866''7504'_'8758'_'8680''91'_'93'__18
                    T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'curry_470 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'cata_484 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                    T__'8866''7580'_'8758'_'10814'__24 |
    C_m'45'arr_494 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_m'45'const_504 T__'8866''7501'_'8758'__14 | C_m'45'named_516
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__24 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__24
  = C_t'45'morph'45'lift_528 T__'8866''7504'_'8758'_'8680''91'_'93'__18 |
    C_t'45'embed_538 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_556 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'value'45'lift_566 T__'8866''7501'_'8758'__14 |
    C_t'45'pair'45'lit'45'check_582 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__24
                                    T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'In'45'app'45'check_594 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                  T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'apply'45'check_606 MAlonzo.Code.Once.Type.T_Type_112
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_618 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'inr'45'app'45'check_630 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'initial'45'app'45'check_640 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'arr'45'app'45'check_652 T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'arg'45'driven'45'app'45'check_668 MAlonzo.Code.Once.Type.T_Type_112
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__24 |
    C_t'45'var'45'poly'45'instantiate_680 MAlonzo.Code.Once.Type.T_PolyType_244
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          T__'8866''7580'_'8758'_'10814'__24
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__686 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__686 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_698 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d_Typed_698 = erased
-- Once.TypeCheck.Judgment.extractMorphWitness
d_extractMorphWitness_720 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_extractMorphWitness_720 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_extractMorphWitness_720 v1 v6
du_extractMorphWitness_720 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T__'8866''7580'_'8758'_'10814'__24 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_extractMorphWitness_720 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         C_t'45'morph'45'lift_528 v8
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
         C_t'45'embed_538 v7
           -> case coe v7 of
                C_t'45'var'45'import_82
                  -> case coe v0 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'named_516)
                       _ -> coe v2
                _ -> coe v2
         C_t'45'value'45'lift_566 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'const_504 v7)
         C_t'45'arr'45'app'45'check_652 v8
           -> case coe v0 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> coe
                       du_extractMorph'45'arr_730
                       (coe du_extractMorphWitness_720 (coe v10) (coe v8))
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Judgment.extractMorph-arr
d_extractMorph'45'arr_730 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_extractMorph'45'arr_730 ~v0 ~v1 ~v2 ~v3 v4
  = du_extractMorph'45'arr_730 v4
du_extractMorph'45'arr_730 ::
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_extractMorph'45'arr_730 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_m'45'arr_494 v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
