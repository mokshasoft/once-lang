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
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_22 | C_t'45'str_28 | C_t'45'unit_32 |
    C_t'45'unit'45'var_36 |
    C_t'45'var'45'local_48 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 |
    C_t'45'var'45'qualified_58 | C_t'45'var'45'import_66 |
    C_t'45'annot_76 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_92 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_100 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'let_120 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_150 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                    MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_164 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_178 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                            MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_188 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_200 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_212 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_222 MAlonzo.Code.Once.Type.T_Type_108
                               MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'arr'45'app'45'infer_234 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_246 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_264 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_280 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                      MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'embed_290 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'lam_308 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'id'45'check_314 | C_t'45'fst'45'check_322 |
    C_t'45'snd'45'check_330 | C_t'45'terminal'45'check_336 |
    C_t'45'initial'45'check_342 | C_t'45'inl'45'check_350 |
    C_t'45'inr'45'check_358 | C_t'45'arr'45'check_366 |
    C_t'45'pair'45'check_384 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                             T__'8866''7580'_'8758'_'10814'__16
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check_402 MAlonzo.Code.Once.Type.T_Type_108
                                MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                T__'8866''7580'_'8758'_'10814'__16
                                T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_416 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                              T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_428 MAlonzo.Code.Once.Type.T_Type_108
                              MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_440 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_452 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_462 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'arr'45'app'45'check_474 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'arg'45'driven'45'app'45'check_490 MAlonzo.Code.Once.Type.T_Type_108
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                             MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_502 MAlonzo.Code.Once.Type.T_PolyType_232
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          T__'8866''7580'_'8758'_'10814'__16
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__508 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_136 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 -> ()
d__'8866'_'8758'_'10814'__508 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_520 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_136 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 -> ()
d_Typed_520 = erased
