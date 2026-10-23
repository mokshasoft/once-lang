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
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Typing._⊢ᵢ_∶_⨾_
d__'8866''7522'_'8758'_'10814'__12 a0 a1 a2 a3 a4 = ()
data T__'8866''7522'_'8758'_'10814'__12
  = C_t'45'int_38 | C_t'45'float_48 | C_t'45'unit_52 |
    C_t'45'unit'45'var_56 |
    C_t'45'var'45'local_68 MAlonzo.Code.Once.Internal.Context.T_SVar_66 |
    C_t'45'var'45'resolved_78 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                              MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 AgdaAny
                              MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_t'45'var'45'own_88 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_t'45'var'45'import_98 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_t'45'var'45'poly'45'instantiate'45'infer_114 MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                                                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_126 T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair_142 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7522'_'8758'_'10814'__12
                    T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg_150 T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg'45'float_160 |
    C_t'45'let_180 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'case_214 MAlonzo.Code.Once.Spec.Type.T_Ty_8
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
    C_t'45'binop'45'arith_228 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float_242 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7522'_'8758'_'10814'__12
                                       T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'il_256 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'ir_270 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'cmp_284 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'id'45'app_294 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'fst'45'app_306 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'snd'45'app_318 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'terminal'45'app_328 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                               MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'app'45'infer_340 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'eff'45'app'45'infer_356 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                            MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'app'45'infer_368 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'eff'45'app'45'infer_380 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                          MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'app_398 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'effApp_418 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                      T__'8866''7522'_'8758'_'10814'__12
                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'app'45'spine_434 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
-- Once.Internal.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__20 a0 a1 a2 a3 a4 = ()
data T__'8866''7580'_'8758'_'10814'__20
  = C_t'45'id'45'check_446 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'fst'45'check_458 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'snd'45'check_470 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'terminal'45'morph'45'check_480 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'initial'45'morph'45'check_490 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inl'45'morph'45'check_502 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inr'45'morph'45'check_514 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'compose'45'check'45'g_534 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'compose'45'check'45'f_558 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12
                                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'case'45'copair'45'check_578 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'morph'45'check_598 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      T__'8866''7580'_'8758'_'10814'__20
                                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'curry'45'check_618 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                              T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'cata'45'check_634 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                             MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'ana'45'check_654 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                            T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'loop'45'check_666 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'sub_678 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   T__'8866''7522'_'8758'_'10814'__12
                   MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 |
    C_t'45'lam_700 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'lit'45'check_716 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    T__'8866''7580'_'8758'_'10814'__20
                                    T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'In'45'app'45'check_726 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                  MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                  T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'apply'45'check_738 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'inl'45'app'45'check_750 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'inr'45'app'45'check_762 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'initial'45'app'45'check_772 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'var'45'poly'45'instantiate_786 MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Internal.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 a0 a1 a2
                                                         a3 a4 a5 a6
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
  = C_d'45'infer_806 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                     T__'8866''7522'_'8758'_'10814'__12
                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                     MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'poly_830 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                    [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                    MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_260
                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'lam_850 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_d'45'compose_870 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'id_880 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'fst_892 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'snd_904 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'terminal_914 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'initial_922 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'case_946 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_d'45'pair_966 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'cata_982 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                    MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                    T__'8866''7522'_'8758'_'10814'__12
-- Once.Internal.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__990 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d__'8866'_'8758'_'10814'__990 = erased
-- Once.Internal.Typing.Typed
d_Typed_1004 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_Typed_1004 = erased
