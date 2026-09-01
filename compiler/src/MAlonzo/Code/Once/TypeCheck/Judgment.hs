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
  = C_t'45'int_22 | C_t'45'float_34 | C_t'45'str_40 |
    C_t'45'unit_44 | C_t'45'unit'45'var_48 |
    C_t'45'var'45'local_60 MAlonzo.Code.Once.Surface.Context.T_SVar_210 |
    C_t'45'var'45'qualified_70 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'resolved_78 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'import_86 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_t'45'var'45'poly'45'instantiate'45'infer_102 MAlonzo.Code.Once.Type.T_PolyType_240
                                                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'annot_112 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_128 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_136 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_148 |
    C_t'45'let_168 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_198 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_212 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_226 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_240 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_254 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_268 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_278 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_290 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_302 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_312 MAlonzo.Code.Once.Type.T_Type_108
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_324 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_342 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_358 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_366 | C_t'45'fst'45'check_376 |
    C_t'45'snd'45'check_386 | C_t'45'terminal'45'morph'45'check_394 |
    C_t'45'initial'45'morph'45'check_402 |
    C_t'45'inl'45'morph'45'check_412 |
    C_t'45'inr'45'morph'45'check_422 |
    C_t'45'compose'45'check_442 MAlonzo.Code.Once.Type.T_Type_108
                                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                T__'8866''7580'_'8758'_'10814'__16
                                T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_462 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_480 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_494 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_506 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'embed_516 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_534 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_550 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_560 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_572 MAlonzo.Code.Once.Type.T_Type_108
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_584 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_596 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_606 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'subsume_618 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'arg'45'driven'45'app'45'check_634 MAlonzo.Code.Once.Type.T_Type_108
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_648 MAlonzo.Code.Once.Type.T_PolyType_240
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          T__'8866''7580'_'8758'_'10814'__16
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__654 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__654 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_666 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_666 = erased
