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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_26 | C_t'45'str_32 | C_t'45'unit_36 |
    C_t'45'unit'45'var_40 |
    C_t'45'var'45'local_52 MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 |
    C_t'45'var'45'qualified_62 | C_t'45'var'45'import_70 |
    C_t'45'annot_80 T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair_96 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_104 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'let_124 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_154 MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Type_112
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_168 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_182 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                            MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_192 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_204 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_216 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_226 MAlonzo.Code.Once.Type.T_Type_112
                               MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'arr'45'app'45'infer_238 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_250 MAlonzo.Code.Once.Type.T_Type_112
                                     MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_268 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'effApp_284 MAlonzo.Code.Once.Type.T_Type_112
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__20
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
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__20 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__20
  = C_t'45'embed_346 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_364 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'id'45'check_370 | C_t'45'fst'45'check_378 |
    C_t'45'snd'45'check_386 | C_t'45'terminal'45'check_392 |
    C_t'45'value'45'lift_402 T__'8866''7501'_'8758'__14 |
    C_t'45'initial'45'check_408 | C_t'45'inl'45'check_416 |
    C_t'45'inr'45'check_424 | C_t'45'arr'45'check_432 |
    C_t'45'pair'45'check_450 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                             T__'8866''7580'_'8758'_'10814'__20
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'lit'45'check_466 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__20
                                    T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'case'45'copair'45'check_486 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__20
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'In'45'app'45'check_498 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                  T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'cata'45'check_512 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'compose'45'check_532 MAlonzo.Code.Once.Type.T_Type_112
                                MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                T__'8866''7580'_'8758'_'10814'__20
                                T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'curry'45'check_546 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'apply'45'check_558 MAlonzo.Code.Once.Type.T_Type_112
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_570 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'inr'45'app'45'check_582 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'initial'45'app'45'check_592 MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'arr'45'app'45'check_604 T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'arg'45'driven'45'app'45'check_620 MAlonzo.Code.Once.Type.T_Type_112
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'var'45'poly'45'instantiate_632 MAlonzo.Code.Once.Type.T_PolyType_240
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          T__'8866''7580'_'8758'_'10814'__20
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_136 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__638 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_650 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_136 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 -> ()
d_Typed_650 = erased
