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
    C_t'45'var'45'poly'45'instantiate'45'infer_104 MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                                                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                                                   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] AgdaAny
                                                   AgdaAny |
    C_t'45'annot_116 T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair_132 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7522'_'8758'_'10814'__12
                    T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg_140 T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'neg'45'float_150 |
    C_t'45'let_170 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'case_204 MAlonzo.Code.Once.Spec.Type.T_Ty_8
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
    C_t'45'binop'45'arith_218 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float_232 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7522'_'8758'_'10814'__12
                                       T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'il_246 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'arith'45'float'45'ir_260 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                             T__'8866''7522'_'8758'_'10814'__12
                                             T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'binop'45'cmp_274 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'id'45'app_284 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'fst'45'app_296 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'snd'45'app_308 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'terminal'45'app_318 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                               MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'app'45'infer_330 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'apply'45'eff'45'app'45'infer_346 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                            MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                                            T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'app'45'infer_358 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                   T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'Out'45'eff'45'app'45'infer_370 MAlonzo.Code.Once.Spec.Type.T_Fun_12
                                          MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                          MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                          T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'app_388 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   T__'8866''7522'_'8758'_'10814'__12
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'effApp_408 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                      T__'8866''7522'_'8758'_'10814'__12
                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'app'45'spine_424 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T__'8866''7522'_'8758'_'10814'__12
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
-- Once.Internal.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__20 a0 a1 a2 a3 a4 = ()
data T__'8866''7580'_'8758'_'10814'__20
  = C_t'45'id'45'check_436 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'fst'45'check_448 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'snd'45'check_460 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'terminal'45'morph'45'check_470 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'initial'45'morph'45'check_480 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inl'45'morph'45'check_492 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'inr'45'morph'45'check_504 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_t'45'compose'45'check'45'g_524 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'compose'45'check'45'f_548 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                     T__'8866''7522'_'8758'_'10814'__12
                                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                                     T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'case'45'copair'45'check_568 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'morph'45'check_588 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                      T__'8866''7580'_'8758'_'10814'__20
                                      T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'curry'45'check_608 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                              T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'cata'45'check_624 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                             MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'ana'45'check_644 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                            MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                            T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'loop'45'check_656 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'sub_668 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   T__'8866''7522'_'8758'_'10814'__12
                   MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 |
    C_t'45'lam_690 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'pair'45'lit'45'check_706 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    T__'8866''7580'_'8758'_'10814'__20
                                    T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'In'45'app'45'check_716 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                  MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                  T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'apply'45'check_728 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              T__'8866''7522'_'8758'_'10814'__12 |
    C_t'45'inl'45'app'45'check_740 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'inr'45'app'45'check_752 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'initial'45'app'45'check_762 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                       T__'8866''7580'_'8758'_'10814'__20 |
    C_t'45'var'45'poly'45'instantiate_776 MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Internal.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 a0 a1 a2
                                                         a3 a4 a5 a6
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
  = C_d'45'infer_796 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                     MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                     T__'8866''7522'_'8758'_'10814'__12
                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                     MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'poly_820 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                    [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                    MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316
                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'lam_840 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   T__'8866''7522'_'8758'_'10814'__12 |
    C_d'45'compose_860 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'id_870 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'fst_882 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'snd_894 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'terminal_904 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'initial_912 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'case_936 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_d'45'pair_956 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 |
    C_d'45'cata_972 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                    MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                    T__'8866''7522'_'8758'_'10814'__12
-- Once.Internal.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__980 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d__'8866'_'8758'_'10814'__980 = erased
-- Once.Internal.Typing.Typed
d_Typed_994 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_Typed_994 = erased
