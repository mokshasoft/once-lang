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

module MAlonzo.Code.Once.TypeCheck.Use where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Surface.Typing
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.TypeCheck.Use.SU._∋_⦂_at_
d__'8715'_'10626'_at__22 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.TypeCheck.Use.SU._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__24 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12
  = ()
-- Once.TypeCheck.Use.SU._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__26 a0 a1 a2 a3 a4 a5
                                                  a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.TypeCheck.Use.SU._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12
  = ()
-- Once.TypeCheck.Use.SU.Locals
d_Locals_38 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.TypeCheck.Use._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__416 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 -> ()
d__'8866'_'8658'_'8605'__416 = erased
-- Once.TypeCheck.Use._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__420 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 -> ()
d__'8866'_'8656'_'8605'__420 = erased
-- Once.TypeCheck.Use._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__424 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 -> ()
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__424 = erased
-- Once.TypeCheck.Use.ctxOf
d_ctxOf_428 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d_ctxOf_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_ctxOf_428 v7
du_ctxOf_428 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
du_ctxOf_428 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Typing.C_'8709'_22
        -> coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12
      MAlonzo.Code.Once.Spec.Surface.Typing.C__'9657'_'8758'__26 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16
             (coe du_ctxOf_428 (coe v2)) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Use.lookup-at
d_lookup'45'at_444 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T__'8715'_'10626'_at__32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'at_444 = erased
-- Once.TypeCheck.Use.Use⇒
d_Use'8658'_458 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_Use'8658'_458
  = C_u'45'int_494 | C_u'45'float_502 | C_u'45'unit_504 |
    C_u'45'unit'45'g_506 | C_u'45'var_516 |
    C_u'45'sigop_528 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                     MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_u'45'def_540 | C_u'45'annot_552 T_Use'8656'_470 |
    C_u'45'pair_574 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                    T_Use'8658'_458 |
    C_u'45'neg_584 T_Use'8658'_458 | C_u'45'neg'45'float_592 |
    C_u'45'let_618 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                   T_Use'8658'_458 |
    C_u'45'case_664 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                    T_Use'8658'_458 T_Use'8658'_458 |
    C_u'45'arith_688 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                     T_Use'8658'_458 |
    C_u'45'arith'45'float_712 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                              T_Use'8658'_458 |
    C_u'45'arith'45'float'45'il_736 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                                    T_Use'8658'_458 |
    C_u'45'arith'45'float'45'ir_760 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                                    T_Use'8658'_458 |
    C_u'45'compare_784 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                       T_Use'8658'_458 |
    C_u'45'id'45'app_796 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T_Use'8658'_458 |
    C_u'45'fst'45'app_810 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_458 |
    C_u'45'snd'45'app_824 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_458 |
    C_u'45'terminal'45'app_836 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8658'_458 |
    C_u'45'apply'45'app_850 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T_Use'8658'_458 |
    C_u'45'apply'45'eff'45'app_868 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T_Use'8658'_458 |
    C_u'45'Out'45'app_882 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_458 |
    C_u'45'Out'45'act'45'app_896 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                 T_Use'8658'_458 |
    C_u'45'app_922 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                   T_Use'8656'_470 |
    C_u'45'effApp_950 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                      T_Use'8656'_470 |
    C_u'45'app'45'spine_974 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                            T_Use'8614'_486
-- Once.TypeCheck.Use.Use⇐
d_Use'8656'_470 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_Use'8656'_470
  = C_u'45'id_984 | C_u'45'fst_992 | C_u'45'snd_1000 |
    C_u'45'terminal_1006 | C_u'45'initial_1012 | C_u'45'inl_1020 |
    C_u'45'inr_1028 |
    C_u'45'compose'45'g_1054 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_486
                             T_Use'8656'_470 |
    C_u'45'compose'45'f_1086 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_458
                             T_Use'8656'_470 |
    C_u'45'case_1112 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_470
                     T_Use'8656'_470 |
    C_u'45'pair_1138 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_470
                     T_Use'8656'_470 |
    C_u'45'curry_1158 T_Use'8656'_470 |
    C_u'45'cata_1176 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_470 |
    C_u'45'ana_1198 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T_Use'8656'_470 |
    C_u'45'loop_1212 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_470 |
    C_u'45'sub_1228 T_Use'8658'_458 |
    C_u'45'lam_1250 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8656'_470 |
    C_u'45'pair'45'lit_1272 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_470
                            T_Use'8656'_470 |
    C_u'45'In'45'app_1286 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8656'_470 |
    C_u'45'apply'45'app_1300 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T_Use'8658'_458 |
    C_u'45'inl'45'app_1314 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_470 |
    C_u'45'inr'45'app_1328 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_470 |
    C_u'45'initial'45'app_1340 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8656'_470 |
    C_u'45'poly_1354
-- Once.TypeCheck.Use.Use↦
d_Use'8614'_486 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_Use'8614'_486
  = C_u'45'infer_1382 T_Use'8658'_458 | C_u'45'poly_1418 |
    C_u'45'lam_1438 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8658'_458 |
    C_u'45'compose_1464 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                        MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_486
                        T_Use'8614'_486 |
    C_u'45'id_1470 | C_u'45'fst_1478 | C_u'45'snd_1486 |
    C_u'45'terminal_1492 | C_u'45'initial_1496 |
    C_u'45'case_1528 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_486
                     T_Use'8614'_486 |
    C_u'45'pair_1554 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_486
                     T_Use'8614'_486 |
    C_u'45'cata_1572 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8658'_458
