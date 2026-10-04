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
    C_t'45'var'45'import_88 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 |
    C_t'45'var'45'poly'45'instantiate'45'infer_104 MAlonzo.Code.Once.Type.T_PolyType_254
                                                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_114 MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_130 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_138 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_150 |
    C_t'45'let_170 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_200 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_214 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_228 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_242 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_256 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_270 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_280 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_292 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_304 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_314 MAlonzo.Code.Once.Type.T_Type_108
                               MAlonzo.Code.Once.Surface.Context.T_Usage_60
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_326 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_338 MAlonzo.Code.Once.Type.T_Type_108
                                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_350 MAlonzo.Code.Once.Type.T_Functor_106
                                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_362 MAlonzo.Code.Once.Type.T_Functor_106
                                          MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                          MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_380 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_Quantity_4
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_396 MAlonzo.Code.Once.Type.T_Type_108
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_412 MAlonzo.Code.Once.Type.T_Type_108
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
-- Once.TypeCheck.Judgment._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_420 | C_t'45'fst'45'check_430 |
    C_t'45'snd'45'check_440 | C_t'45'terminal'45'morph'45'check_448 |
    C_t'45'initial'45'morph'45'check_456 |
    C_t'45'inl'45'morph'45'check_466 |
    C_t'45'inr'45'morph'45'check_476 |
    C_t'45'compose'45'check'45'g_496 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_520 MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Type_108
                                     MAlonzo.Code.Once.Type.T_Purity_32
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_540 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_560 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_578 T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_592 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_606 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_618 MAlonzo.Code.Once.Type.T_Type_108
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 |
    C_t'45'lam_638 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_654 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_664 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_676 MAlonzo.Code.Once.Type.T_Type_108
                              MAlonzo.Code.Once.Surface.Context.T_Usage_60
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_688 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_700 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_710 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_724 MAlonzo.Code.Once.Type.T_PolyType_254
                                          MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.TypeCheck.Judgment._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_742 MAlonzo.Code.Once.Type.T_Type_108
                     MAlonzo.Code.Once.Type.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
                     MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_d'45'poly_766 MAlonzo.Code.Once.Type.T_Purity_32
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
    C_d'45'lam_784 MAlonzo.Code.Once.Type.T_Quantity_4
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_804 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_812 | C_d'45'fst_822 | C_d'45'snd_832 |
    C_d'45'terminal_840 | C_d'45'initial_846 |
    C_d'45'case_866 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'pair_886 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_900 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                    T__'8866''7522'_'8758'_'10814'__10
-- Once.TypeCheck.Judgment._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__906 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d__'8866'_'8758'_'10814'__906 = erased
-- Once.TypeCheck.Judgment.Typed
d_Typed_918 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> ()
d_Typed_918 = erased
