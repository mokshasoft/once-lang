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
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_30 | C_t'45'float_42 | C_t'45'str_48 |
    C_t'45'unit_52 | C_t'45'unit'45'var_56 |
    C_t'45'var'45'local_68 MAlonzo.Code.Once.Surface.Context.T_SVar_210 |
    C_t'45'var'45'qualified_78 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
                               AgdaAny |
    C_t'45'var'45'resolved_86 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                              MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 AgdaAny |
    C_t'45'var'45'import_94 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
                            AgdaAny |
    C_t'45'var'45'poly'45'instantiate'45'infer_110 MAlonzo.Code.Once.Type.T_PolyType_246
                                                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'annot_120 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_136 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_144 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_156 |
    C_t'45'let_176 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_206 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Type_108
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
    C_t'45'fst'45'app_298 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_310 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_320 MAlonzo.Code.Once.Type.T_Type_108
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_332 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_344 MAlonzo.Code.Once.Type.T_Type_108
                                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_356 MAlonzo.Code.Once.Type.T_Functor_106
                                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_368 MAlonzo.Code.Once.Type.T_Functor_106
                                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                          MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_386 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_402 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_418 MAlonzo.Code.Once.Type.T_Type_108
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_t'45'neg'45'void_426 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case'45'void_454 MAlonzo.Code.Once.Type.T_Type_108
                            MAlonzo.Code.Once.Type.T_Type_108
                            MAlonzo.Code.Once.Type.T_Quantity_4
                            MAlonzo.Code.Once.Type.T_Quantity_4
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'void'45'l_470 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7522'_'8758'_'10814'__10
                                  T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'void'45'r_486 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7522'_'8758'_'10814'__10
                                  T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app'45'void_494 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app'45'void_502 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'void_510 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'void_518 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app'45'void_532 MAlonzo.Code.Once.Type.T_Type_108
                           MAlonzo.Code.Once.Surface.Context.T_Usage_60
                           T__'8866''7522'_'8758'_'10814'__10
                           T__'8866''7522'_'8758'_'10814'__10
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_540 | C_t'45'fst'45'check_550 |
    C_t'45'snd'45'check_560 | C_t'45'terminal'45'morph'45'check_568 |
    C_t'45'initial'45'morph'45'check_576 |
    C_t'45'inl'45'morph'45'check_586 |
    C_t'45'inr'45'morph'45'check_596 |
    C_t'45'compose'45'check'45'g_616 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_640 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Purity_32
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__44
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_660 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_680 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_698 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_710 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_724 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_736 MAlonzo.Code.Once.Type.T_Type_108
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 |
    C_t'45'lam_756 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_772 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_782 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_794 MAlonzo.Code.Once.Type.T_Type_108
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_806 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_818 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_828 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_842 MAlonzo.Code.Once.Type.T_PolyType_246
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          T__'8866''7580'_'8758'_'10814'__16
-- Once.TypeCheck.Judgment._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_860 MAlonzo.Code.Once.Type.T_Type_108
                     MAlonzo.Code.Once.Type.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__44
                     MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_d'45'lam_878 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_898 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_906 | C_d'45'fst_916 | C_d'45'snd_926 |
    C_d'45'terminal_934 | C_d'45'initial_940 |
    C_d'45'case_960 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'pair_980 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_992 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'fst'45'void_998 | C_d'45'snd'45'void_1004 |
    C_d'45'case'45'void_1022 MAlonzo.Code.Once.Type.T_Type_108
                             MAlonzo.Code.Once.Type.T_Type_108
                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                             T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                             T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata'45'void_1032 MAlonzo.Code.Once.Type.T_Type_108
                             T__'8866''7522'_'8758'_'10814'__10
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__1038 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__1038 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_1050 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_1050 = erased
