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
    C_t'45'var'45'resolved_70 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                              MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'own_78 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'import_86 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 |
    C_t'45'var'45'poly'45'instantiate'45'infer_102 MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                                                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_112 MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair_128 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg_136 T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'neg'45'float_148 |
    C_t'45'let_168 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'case_198 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith_212 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_226 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_240 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_254 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_268 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_278 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_290 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_302 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_312 MAlonzo.Code.Once.Lang.Type.T_Type_8
                               MAlonzo.Code.Once.Lang.Context.T_Usage_46
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_324 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_340 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                            MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_352 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_364 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                          MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_382 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_402 MAlonzo.Code.Once.Lang.Type.T_Type_8
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_418 MAlonzo.Code.Once.Lang.Type.T_Type_8
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
-- Once.Lang.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_428 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'fst'45'check_440 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'snd'45'check_452 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'terminal'45'morph'45'check_462 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'initial'45'morph'45'check_472 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inl'45'morph'45'check_484 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inr'45'morph'45'check_496 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'compose'45'check'45'g_516 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_540 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_560 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_580 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_600 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                              T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_616 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                             MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                             MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_636 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'loop'45'check_648 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_660 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 |
    C_t'45'lam_682 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_698 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_708 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_720 MAlonzo.Code.Once.Lang.Type.T_Type_8
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_732 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_744 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_754 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_768 MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                                          MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Lang.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_786 MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'poly_810 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
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
    C_d'45'lam_830 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_850 MAlonzo.Code.Once.Lang.Type.T_Type_8
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_860 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'fst_872 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'snd_884 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'terminal_894 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'initial_902 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'case_922 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'pair_942 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_958 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                    MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                    T__'8866''7522'_'8758'_'10814'__10
-- Once.Lang.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__964 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d__'8866'_'8758'_'10814'__964 = erased
-- Once.Lang.Typing.Typed
d_Typed_976 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d_Typed_976 = erased
