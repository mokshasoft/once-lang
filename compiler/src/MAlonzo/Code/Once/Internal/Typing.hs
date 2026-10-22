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

module MAlonzo.Code.Once.Internal.Typing where

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
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Typing._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__12 a0 a1 a2 a3 a4 = ()
data T__'8866''7522'_'8758'_'10814'__12
  = C_t'45'int_38 | C_t'45'float_50 | C_t'45'unit_54 |
    C_t'45'unit'45'var_58 |
    C_t'45'var'45'local_70 MAlonzo.Code.Once.Internal.Context.T_SVar_66 |
    C_t'45'var'45'resolved_80 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                              MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 AgdaAny
                              MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_t'45'var'45'own_90 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_t'45'var'45'import_100 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                             MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_t'45'var'45'poly'45'instantiate'45'infer_116 MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10
                                                   MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_128 MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_58
                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair_144 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7522'_'8758'_'10814'__12
                    T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg_152 T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg'45'float_164 |
    C_t'45'let_184 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'case_218 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7522'_'8758'_'10814'__12
                    T__'8866''7522'_'8758'_'10814'__12
                    T__'8866''7522'_'8758'_'10814'__12
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_t'45'binop'45'arith_232 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float_246 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7522'_'8758'_'10814'__12
                                       T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'il_260 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'ir_274 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'cmp_288 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'id'45'app_298 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'fst'45'app_310 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'snd'45'app_322 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'terminal'45'app_332 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                               MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'app'45'infer_344 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'eff'45'app'45'infer_360 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                            MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'app'45'infer_372 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'eff'45'app'45'infer_384 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                          MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'app_402 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'effApp_422 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                      T__'8866''7522'_'8758'_'10814'__12
                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'app'45'spine_438 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
-- Once.Internal.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__20 a0 a1 a2 a3 a4 = ()
data T__'8866''7580'_'8758'_'10814'__20
  = C_t'45'id'45'check_450 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'fst'45'check_462 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'snd'45'check_474 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'terminal'45'morph'45'check_484 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'initial'45'morph'45'check_494 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inl'45'morph'45'check_506 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inr'45'morph'45'check_518 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'compose'45'check'45'g_538 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'compose'45'check'45'f_562 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12
                                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'case'45'copair'45'check_582 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'morph'45'check_602 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      T__'8866''7580'_'8758'_'10814'__20
                                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'curry'45'check_622 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                              T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'cata'45'check_638 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                             MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'ana'45'check_658 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                            T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'loop'45'check_670 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'sub_682 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   T__'8866''7522'_'8758'_'10814'__12
                   MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 |
    C_t'45'lam_704 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'lit'45'check_720 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    T__'8866''7580'_'8758'_'10814'__20
                                    T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'In'45'app'45'check_730 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                  MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                  T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'apply'45'check_742 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'inl'45'app'45'check_754 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'inr'45'app'45'check_766 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'initial'45'app'45'check_776 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'var'45'poly'45'instantiate_790 MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10
                                          MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Internal.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 a0 a1 a2
                                                         a3 a4 a5 a6
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
  = C_d'45'infer_810 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                     T__'8866''7522'_'8758'_'10814'__12
                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                     MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'poly_834 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                    MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10
                    MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34
                    [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                    MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_296
                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'lam_854 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_d'45'compose_874 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'id_884 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'fst_896 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'snd_908 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'terminal_918 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'initial_926 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'case_950 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_d'45'pair_970 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'cata_986 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                    MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                    T__'8866''7522'_'8758'_'10814'__12
-- Once.Internal.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__994 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d__'8866'_'8758'_'10814'__994 = erased
-- Once.Internal.Typing.Typed
d_Typed_1008 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_Typed_1008 = erased
