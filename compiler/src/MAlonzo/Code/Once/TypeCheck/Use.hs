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
d__'8715'_'10626'_at__26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13
  = ()
-- Once.TypeCheck.Use.SU._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12 a13 a14
  = ()
-- Once.TypeCheck.Use.SU._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__30 a0 a1 a2 a3 a4 a5
                                                  a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  = ()
-- Once.TypeCheck.Use.SU._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__32 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12 a13 a14
  = ()
-- Once.TypeCheck.Use.SU.Locals
d_Locals_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.TypeCheck.Use._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__420 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 -> ()
d__'8866'_'8658'_'8605'__420 = erased
-- Once.TypeCheck.Use._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__424 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 -> ()
d__'8866'_'8656'_'8605'__424 = erased
-- Once.TypeCheck.Use._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__428 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
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
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__428 = erased
-- Once.TypeCheck.Use.Shape
d_Shape_432 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Shape_432
  = C_sh'45''8709'_434 | C_sh'45''9656'_446 T_Shape_432
-- Once.TypeCheck.Use.lookup-shape
d_lookup'45'shape_460 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  T_Shape_432 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T__'8715'_'10626'_at__32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'shape_460 = erased
-- Once.TypeCheck.Use.ctxOf
d_ctxOf_470 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d_ctxOf_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_ctxOf_470 v9
du_ctxOf_470 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
du_ctxOf_470 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Typing.C_'8709'_22
        -> coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12
      MAlonzo.Code.Once.Spec.Surface.Typing.C__'9657'_'8758'__26 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16
             (coe du_ctxOf_470 (coe v2)) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Use.shape-of
d_shape'45'of_480 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 -> T_Shape_432
d_shape'45'of_480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_shape'45'of_480 v9
du_shape'45'of_480 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Locals_18 -> T_Shape_432
du_shape'45'of_480 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Typing.C_'8709'_22
        -> coe C_sh'45''8709'_434
      MAlonzo.Code.Once.Spec.Surface.Typing.C__'9657'_'8758'__26 v2 v3 v4
        -> coe C_sh'45''9656'_446 (coe du_shape'45'of_480 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Use.lookup-at
d_lookup'45'at_496 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
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
d_lookup'45'at_496 = erased
-- Once.TypeCheck.Use.Use⇒
d_Use'8658'_510 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_Use'8658'_510
  = C_u'45'int_546 | C_u'45'float_554 | C_u'45'unit_556 |
    C_u'45'unit'45'g_558 | C_u'45'var_568 |
    C_u'45'sigop_580 MAlonzo.Code.Once.Spec.Type.T_Ty_8 AgdaAny
                     MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_8 AgdaAny |
    C_u'45'def_594 AgdaAny | C_u'45'annot_606 T_Use'8656'_522 |
    C_u'45'pair_628 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                    T_Use'8658'_510 |
    C_u'45'neg_638 T_Use'8658'_510 | C_u'45'neg'45'float_646 |
    C_u'45'let_672 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                   T_Use'8658'_510 |
    C_u'45'case_718 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                    T_Use'8658'_510 T_Use'8658'_510 |
    C_u'45'arith_742 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                     T_Use'8658'_510 |
    C_u'45'arith'45'float_766 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                              T_Use'8658'_510 |
    C_u'45'arith'45'float'45'il_790 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                                    T_Use'8658'_510 |
    C_u'45'arith'45'float'45'ir_814 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                    MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                                    T_Use'8658'_510 |
    C_u'45'compare_838 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                       T_Use'8658'_510 |
    C_u'45'id'45'app_850 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                         T_Use'8658'_510 |
    C_u'45'fst'45'app_864 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_510 |
    C_u'45'snd'45'app_878 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_510 |
    C_u'45'terminal'45'app_890 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8658'_510 |
    C_u'45'apply'45'app_904 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            T_Use'8658'_510 |
    C_u'45'apply'45'eff'45'app_922 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                   T_Use'8658'_510 |
    C_u'45'Out'45'app_936 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8658'_510 |
    C_u'45'Out'45'act'45'app_950 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                                 T_Use'8658'_510 |
    C_u'45'app_976 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                   T_Use'8656'_522 |
    C_u'45'effApp_1004 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                       T_Use'8656'_522 |
    C_u'45'app'45'spine_1028 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                             T_Use'8614'_538
-- Once.TypeCheck.Use.Use⇐
d_Use'8656'_522 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_Use'8656'_522
  = C_u'45'id_1038 | C_u'45'fst_1046 | C_u'45'snd_1054 |
    C_u'45'terminal_1060 | C_u'45'initial_1066 | C_u'45'inl_1074 |
    C_u'45'inr_1082 |
    C_u'45'compose'45'g_1108 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_538
                             T_Use'8656'_522 |
    C_u'45'compose'45'f_1140 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8658'_510
                             T_Use'8656'_522 |
    C_u'45'case_1166 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_522
                     T_Use'8656'_522 |
    C_u'45'pair_1192 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_522
                     T_Use'8656'_522 |
    C_u'45'curry_1212 T_Use'8656'_522 |
    C_u'45'cata_1230 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_522 |
    C_u'45'ana_1252 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                    T_Use'8656'_522 |
    C_u'45'loop_1266 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8656'_522 |
    C_u'45'sub_1282 T_Use'8658'_510 |
    C_u'45'lam_1304 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8656'_522 |
    C_u'45'pair'45'lit_1326 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                            MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8656'_522
                            T_Use'8656'_522 |
    C_u'45'In'45'app_1340 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                          T_Use'8656'_522 |
    C_u'45'apply'45'app_1354 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                             T_Use'8658'_510 |
    C_u'45'inl'45'app_1368 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_522 |
    C_u'45'inr'45'app_1382 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                           T_Use'8656'_522 |
    C_u'45'initial'45'app_1394 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                               T_Use'8656'_522 |
    C_u'45'poly_1410 AgdaAny
-- Once.TypeCheck.Use.Use↦
d_Use'8614'_538 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                a15 a16
  = ()
data T_Use'8614'_538
  = C_u'45'infer_1438 T_Use'8658'_510 | C_u'45'poly_1476 AgdaAny |
    C_u'45'lam_1496 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_Use'8658'_510 |
    C_u'45'compose_1522 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                        MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_538
                        T_Use'8614'_538 |
    C_u'45'id_1528 | C_u'45'fst_1536 | C_u'45'snd_1544 |
    C_u'45'terminal_1550 | C_u'45'initial_1554 |
    C_u'45'case_1586 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_538
                     T_Use'8614'_538 |
    C_u'45'pair_1612 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Use'8614'_538
                     T_Use'8614'_538 |
    C_u'45'cata_1630 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                     T_Use'8658'_510
