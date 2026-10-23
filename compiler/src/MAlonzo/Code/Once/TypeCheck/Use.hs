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
-- Once.TypeCheck.Use.Shape
d_Shape_428 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Shape_428
  = C_sh'45''8709'_430 | C_sh'45''9656'_442 T_Shape_428
-- Once.TypeCheck.Use.lookup-shape
d_lookup'45'shape_456 ::
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
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  T_Shape_428 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T__'8715'_'10626'_at__32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'shape_456 = erased
-- Once.TypeCheck.Use.ctxOf
d_ctxOf_466 ::
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
d_ctxOf_466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_ctxOf_466 v7
du_ctxOf_466 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
du_ctxOf_466 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Typing.C_'8709'_22
        -> coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12
      MAlonzo.Code.Once.Spec.Surface.Typing.C__'9657'_'8758'__26 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16
             (coe du_ctxOf_466 (coe v2)) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Use.shape-of
d_shape'45'of_476 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 -> T_Shape_428
d_shape'45'of_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_shape'45'of_476 v7
du_shape'45'of_476 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 -> T_Shape_428
du_shape'45'of_476 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Typing.C_'8709'_22
        -> coe C_sh'45''8709'_430
      MAlonzo.Code.Once.Spec.Surface.Typing.C__'9657'_'8758'__26 v2 v3 v4
        -> coe C_sh'45''9656'_442 (coe du_shape'45'of_476 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Use.lookup-at
d_lookup'45'at_492 ::
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
d_lookup'45'at_492 = erased
-- Once.TypeCheck.Use.Use⇒
d_Use'8658'_506 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_Use'8658'_506
  = C_u'45'int_542 | C_u'45'float_550 | C_u'45'unit_552 |
    C_u'45'unit'45'g_554 | C_u'45'var_564 |
    C_u'45'sigop_576 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                     MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 |
    C_u'45'def_588 | C_u'45'annot_600 T_Use'8656'_518 |
    C_u'45'pair_622 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                    T_Use'8658'_506 |
    C_u'45'neg_632 T_Use'8658'_506 | C_u'45'neg'45'float_640 |
    C_u'45'let_666 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                   T_Use'8658'_506 |
    C_u'45'case_712 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                    T_Use'8658'_506 T_Use'8658'_506 |
    C_u'45'arith_736 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                     T_Use'8658'_506 |
    C_u'45'arith'45'float_760 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                              T_Use'8658'_506 |
    C_u'45'arith'45'float'45'il_784 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                                    T_Use'8658'_506 |
    C_u'45'arith'45'float'45'ir_808 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                                    T_Use'8658'_506 |
    C_u'45'compare_832 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                       T_Use'8658'_506 |
    C_u'45'id'45'app_844 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T_Use'8658'_506 |
    C_u'45'fst'45'app_858 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_506 |
    C_u'45'snd'45'app_872 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_506 |
    C_u'45'terminal'45'app_884 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8658'_506 |
    C_u'45'apply'45'app_898 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T_Use'8658'_506 |
    C_u'45'apply'45'eff'45'app_916 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T_Use'8658'_506 |
    C_u'45'Out'45'app_930 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_506 |
    C_u'45'Out'45'act'45'app_944 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                 T_Use'8658'_506 |
    C_u'45'app_970 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                   T_Use'8656'_518 |
    C_u'45'effApp_998 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                      MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                      T_Use'8656'_518 |
    C_u'45'app'45'spine_1022 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                             T_Use'8614'_534
-- Once.TypeCheck.Use.Use⇐
d_Use'8656'_518 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_Use'8656'_518
  = C_u'45'id_1032 | C_u'45'fst_1040 | C_u'45'snd_1048 |
    C_u'45'terminal_1054 | C_u'45'initial_1060 | C_u'45'inl_1068 |
    C_u'45'inr_1076 |
    C_u'45'compose'45'g_1102 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_534
                             T_Use'8656'_518 |
    C_u'45'compose'45'f_1134 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_506
                             T_Use'8656'_518 |
    C_u'45'case_1160 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_518
                     T_Use'8656'_518 |
    C_u'45'pair_1186 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_518
                     T_Use'8656'_518 |
    C_u'45'curry_1206 T_Use'8656'_518 |
    C_u'45'cata_1224 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_518 |
    C_u'45'ana_1246 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T_Use'8656'_518 |
    C_u'45'loop_1260 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_518 |
    C_u'45'sub_1276 T_Use'8658'_506 |
    C_u'45'lam_1298 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8656'_518 |
    C_u'45'pair'45'lit_1320 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_518
                            T_Use'8656'_518 |
    C_u'45'In'45'app_1334 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8656'_518 |
    C_u'45'apply'45'app_1348 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T_Use'8658'_506 |
    C_u'45'inl'45'app_1362 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_518 |
    C_u'45'inr'45'app_1376 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_518 |
    C_u'45'initial'45'app_1388 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8656'_518 |
    C_u'45'poly_1402
-- Once.TypeCheck.Use.Use↦
d_Use'8614'_534 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_Use'8614'_534
  = C_u'45'infer_1430 T_Use'8658'_506 | C_u'45'poly_1466 |
    C_u'45'lam_1486 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8658'_506 |
    C_u'45'compose_1512 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                        MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_534
                        T_Use'8614'_534 |
    C_u'45'id_1518 | C_u'45'fst_1526 | C_u'45'snd_1534 |
    C_u'45'terminal_1540 | C_u'45'initial_1544 |
    C_u'45'case_1576 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_534
                     T_Use'8614'_534 |
    C_u'45'pair_1602 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_534
                     T_Use'8614'_534 |
    C_u'45'cata_1620 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8658'_506
