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

module MAlonzo.Code.Once.Lang.Typing where

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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Typing._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__10 a0 a1 a2 a3 = ()
data T__'8866''7522'_'8758'_'10814'__10
  = C_t'45'int_30 | C_t'45'float_42 | C_t'45'unit_46 |
    C_t'45'unit'45'var_50 |
    C_t'45'var'45'local_62 MAlonzo.Code.Once.Lang.Context.T_SVar_112 |
    C_t'45'var'45'qualified_72 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'resolved_80 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                              MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'own_88 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'import_96 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'poly'45'instantiate'45'infer_112 MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                                                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_122 MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_138 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_146 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_158 |
    C_t'45'let_178 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_208 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_222 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_236 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_250 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_264 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_278 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_288 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_300 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_312 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_322 MAlonzo.Code.Once.Lang.Type.T_Type_8
                               MAlonzo.Code.Once.Lang.Context.T_Usage_46
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_334 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_350 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                            MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_362 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_378 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                          MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48
                                          MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_396 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_416 MAlonzo.Code.Once.Lang.Type.T_Type_8
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_432 MAlonzo.Code.Once.Lang.Type.T_Type_8
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
-- Once.Lang.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_442 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'fst'45'check_454 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'snd'45'check_466 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'terminal'45'morph'45'check_476 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'initial'45'morph'45'check_486 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inl'45'morph'45'check_498 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inr'45'morph'45'check_510 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'compose'45'check'45'g_530 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_554 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_574 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_594 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_614 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                              T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_630 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                             MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                             MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_648 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_660 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 |
    C_t'45'var'45'resolved'45'guard_674 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                                        MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                                        MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48
                                        MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'lam_696 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_712 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_722 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_734 MAlonzo.Code.Once.Lang.Type.T_Type_8
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_746 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_758 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_768 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_782 MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                                          MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Lang.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_800 MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'poly_824 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                    [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                    MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286
                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'lam_844 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_864 MAlonzo.Code.Once.Lang.Type.T_Type_8
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_874 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'fst_886 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'snd_898 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'terminal_908 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'initial_916 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'case_936 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'pair_956 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_972 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                    MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                    T__'8866''7522'_'8758'_'10814'__10
-- Once.Lang.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__978 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d__'8866'_'8758'_'10814'__978 = erased
-- Once.Lang.Typing.Typed
d_Typed_990 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d_Typed_990 = erased
