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
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_30 | C_t'45'float_42 | C_t'45'unit_46 |
    C_t'45'unit'45'var_50 |
    C_t'45'var'45'local_62 MAlonzo.Code.Once.Surface.Context.T_SVar_210 |
    C_t'45'var'45'qualified_72 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 |
    C_t'45'var'45'resolved_80 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                              MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 |
    C_t'45'var'45'own_88 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 |
    C_t'45'var'45'import_96 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 |
    C_t'45'var'45'poly'45'instantiate'45'infer_112 MAlonzo.Code.Once.Type.T_PolyType_254
                                                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_122 MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_138 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_146 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_158 |
    C_t'45'let_178 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_208 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_222 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_236 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_250 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_264 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_278 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_288 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_300 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_312 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_322 MAlonzo.Code.Once.Type.T_Type_108
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_334 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_346 MAlonzo.Code.Once.Type.T_Type_108
                                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_358 MAlonzo.Code.Once.Type.T_Functor_106
                                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_370 MAlonzo.Code.Once.Type.T_Functor_106
                                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                          MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_388 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_404 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_420 MAlonzo.Code.Once.Type.T_Type_108
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_428 | C_t'45'fst'45'check_438 |
    C_t'45'snd'45'check_448 | C_t'45'terminal'45'morph'45'check_456 |
    C_t'45'initial'45'morph'45'check_464 |
    C_t'45'inl'45'morph'45'check_474 |
    C_t'45'inr'45'morph'45'check_484 |
    C_t'45'compose'45'check'45'g_504 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_528 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Purity_32
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_548 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_568 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_586 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_600 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                             MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_616 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_628 MAlonzo.Code.Once.Type.T_Type_108
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Type.Sub.T__'60''58'__24 |
    C_t'45'lam_648 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_664 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_674 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_686 MAlonzo.Code.Once.Type.T_Type_108
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_698 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_710 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_720 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_734 MAlonzo.Code.Once.Type.T_PolyType_254
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.TypeCheck.Judgment._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_752 MAlonzo.Code.Once.Type.T_Type_108
                     MAlonzo.Code.Once.Type.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__24
                     MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_d'45'poly_776 MAlonzo.Code.Once.Type.T_Purity_32
                    MAlonzo.Code.Once.Type.T_PolyType_254
                    MAlonzo.Code.Once.Type.T_PolyType_254
                    MAlonzo.Code.Once.Type.T_PolyType_254
                    MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                    [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                    MAlonzo.Code.Once.Type.T_ArrowSchema_668
                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                    MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_d'45'lam_794 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_814 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_822 | C_d'45'fst_832 | C_d'45'snd_842 |
    C_d'45'terminal_850 | C_d'45'initial_856 |
    C_d'45'case_876 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'pair_896 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_910 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                    T__'8866''7522'_'8758'_'10814'__10
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__916 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_928 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_928 = erased
