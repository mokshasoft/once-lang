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
    C_t'45'var'45'own_78 |
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
    C_t'45'case_202 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    T__'8866''7522'_'8758'_'10814'__10
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 |
    C_t'45'binop'45'arith_216 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float_230 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7522'_'8758'_'10814'__10
                                       T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'il_244 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'arith'45'float'45'ir_258 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                             T__'8866''7522'_'8758'_'10814'__10
                                             T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'binop'45'cmp_272 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'id'45'app_282 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                         T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'fst'45'app_294 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'snd'45'app_306 MAlonzo.Code.Once.Lang.Type.T_Type_8
                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'terminal'45'app_316 MAlonzo.Code.Once.Lang.Type.T_Type_8
                               MAlonzo.Code.Once.Lang.Context.T_Usage_46
                               T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'app'45'infer_328 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'apply'45'eff'45'app'45'infer_344 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                            MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56
                                            T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'app'45'infer_356 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                   T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'Out'45'eff'45'app'45'infer_368 MAlonzo.Code.Once.Lang.Type.T_Functor_6
                                          MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                          MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                          T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'app_386 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   MAlonzo.Code.Once.Lang.Context.T_Usage_46
                   T__'8866''7522'_'8758'_'10814'__10
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'effApp_406 MAlonzo.Code.Once.Lang.Type.T_Type_8
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56
                      T__'8866''7522'_'8758'_'10814'__10
                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'app'45'spine_422 MAlonzo.Code.Once.Lang.Type.T_Type_8
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            T__'8866''7522'_'8758'_'10814'__10
                            T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
-- Once.Lang.Typing._⊢ᶜ_∶_⨾_
d__'8866''7580'_'8758'_'10814'__16 a0 a1 a2 a3 = ()
data T__'8866''7580'_'8758'_'10814'__16
  = C_t'45'id'45'check_432 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'fst'45'check_444 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'snd'45'check_456 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'terminal'45'morph'45'check_466 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'initial'45'morph'45'check_476 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inl'45'morph'45'check_488 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'inr'45'morph'45'check_500 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_t'45'compose'45'check'45'g_520 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'compose'45'check'45'f_544 MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                     T__'8866''7522'_'8758'_'10814'__10
                                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
                                     T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'case'45'copair'45'check_564 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'morph'45'check_584 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                      T__'8866''7580'_'8758'_'10814'__16
                                      T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'curry'45'check_604 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                              T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'cata'45'check_620 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                             MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                             MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'ana'45'check_640 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                            T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'loop'45'check_652 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                             T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'sub_664 MAlonzo.Code.Once.Lang.Type.T_Type_8
                   T__'8866''7522'_'8758'_'10814'__10
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 |
    C_t'45'lam_686 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'pair'45'lit'45'check_702 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                    T__'8866''7580'_'8758'_'10814'__16
                                    T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'In'45'app'45'check_712 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                                  T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'apply'45'check_724 MAlonzo.Code.Once.Lang.Type.T_Type_8
                              MAlonzo.Code.Once.Lang.Context.T_Usage_46
                              T__'8866''7522'_'8758'_'10814'__10 |
    C_t'45'inl'45'app'45'check_736 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'inr'45'app'45'check_748 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                   T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'initial'45'app'45'check_758 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                                       T__'8866''7580'_'8758'_'10814'__16 |
    C_t'45'var'45'poly'45'instantiate_772 MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
                                          MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                                          [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Lang.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_
d__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 a0 a1 a2
                                                         a3 a4 a5
  = ()
data T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
  = C_d'45'infer_790 MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     T__'8866''7522'_'8758'_'10814'__10
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'poly_814 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
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
    C_d'45'lam_834 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                   MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                   T__'8866''7522'_'8758'_'10814'__10 |
    C_d'45'compose_854 MAlonzo.Code.Once.Lang.Type.T_Type_8
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                       T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'id_864 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'fst_876 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'snd_888 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'terminal_898 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'initial_906 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_d'45'case_930 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 |
    C_d'45'pair_950 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
                    T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 |
    C_d'45'cata_966 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                    MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                    T__'8866''7522'_'8758'_'10814'__10
-- Once.Lang.Typing._⊢_∶_⨾_
d__'8866'_'8758'_'10814'__972 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d__'8866'_'8758'_'10814'__972 = erased
-- Once.Lang.Typing.Typed
d_Typed_984 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> ()
d_Typed_984 = erased
