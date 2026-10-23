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

module MAlonzo.Code.Once.TypeCheck.Witness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
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
import qualified MAlonzo.Code.Once.TypeCheck.Use

-- Once.TypeCheck.Witness.SU._⇒⟨_⟩_
d__'8658''10216'_'10217'__20 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658''10216'_'10217'__20 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du__'8658''10216'_'10217'__20
du__'8658''10216'_'10217'__20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du__'8658''10216'_'10217'__20 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Surface.Typing.du__'8658''10216'_'10217'__70
      v1 v2 v3
-- Once.TypeCheck.Witness.SU._∋_⦂_at_
d__'8715'_'10626'_at__22 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.TypeCheck.Witness.SU._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__24 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12
  = ()
-- Once.TypeCheck.Witness.SU._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__26 a0 a1 a2 a3 a4 a5
                                                  a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.TypeCheck.Witness.SU._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
                            a12
  = ()
-- Once.TypeCheck.Witness.SU.Compare
d_Compare_32 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.TypeCheck.Witness.SU.FloatArith
d_FloatArith_34 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.TypeCheck.Witness.SU.IntArith
d_IntArith_36 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.TypeCheck.Witness.SU.Locals
d_Locals_38 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.TypeCheck.Witness.SU.SpecialHead
d_SpecialHead_40 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.TypeCheck.Witness.SU.↑
d_'8593'_216 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8593'_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_'8593'_216
du_'8593'_216 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'8593'_216
  = coe MAlonzo.Code.Once.Spec.Surface.Typing.du_'8593'_64
-- Once.TypeCheck.Witness._.Use↦
d_Use'8614'_424 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.TypeCheck.Witness._.Use⇐
d_Use'8656'_426 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.TypeCheck.Witness._.Use⇒
d_Use'8658'_428 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.TypeCheck.Witness.W⇒
d_W'8658'_716 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_W'8658'_716 = erased
-- Once.TypeCheck.Witness.W⇐
d_W'8656'_732 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_W'8656'_732 = erased
-- Once.TypeCheck.Witness.W↦
d_W'8614'_748 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_W'8614'_748 = erased
-- Once.TypeCheck.Witness._.w-int
d_w'45'int_776 ::
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
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'int_776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_w'45'int_776
du_w'45'int_776 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'int_776
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'int_166)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'int_542)
-- Once.TypeCheck.Witness._.w-float
d_w'45'float_786 ::
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
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'float_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'float_786
du_w'45'float_786 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'float_786
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'float_174)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'float_550)
-- Once.TypeCheck.Witness._.w-unit
d_w'45'unit_794 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'unit_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_w'45'unit_794
du_w'45'unit_794 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'unit_794
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'unit_176)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'unit_552)
-- Once.TypeCheck.Witness._.w-unit-g
d_w'45'unit'45'g_796 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'unit'45'g_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_w'45'unit'45'g_796
du_w'45'unit'45'g_796 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'unit'45'g_796
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'unit'45'g_178)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'unit'45'g_554)
-- Once.TypeCheck.Witness._.w-var
d_w'45'var_804 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'var_804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_w'45'var_804 v11
du_w'45'var_804 ::
  MAlonzo.Code.Once.Spec.Surface.Typing.T__'8715'_'10626'_at__32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'var_804 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'var_186 v0)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'var_564)
-- Once.TypeCheck.Witness._.w-sigop
d_w'45'sigop_816 ::
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'sigop_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                 v12 v13 ~v14
  = du_w'45'sigop_816 v10 v11 v12 v13
du_w'45'sigop_816 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'sigop_816 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'sigop_192 v0 v1)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'sigop_576 v2 v3)
-- Once.TypeCheck.Witness._.w-def
d_w'45'def_832 ::
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'def_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12
  = du_w'45'def_832
du_w'45'def_832 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'def_832
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'def_200)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'def_588)
-- Once.TypeCheck.Witness._.w-annot
d_w'45'annot_850 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'annot_850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12
  = du_w'45'annot_850 v12
du_w'45'annot_850 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'annot_850 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'annot_208 v1)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'annot_600 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-pair
d_w'45'pair_872 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'pair_872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 v14 v15 v16 v17
  = du_w'45'pair_872 v14 v15 v16 v17
du_w'45'pair_872 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'pair_872 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'pair_222 v4 v6)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'pair_622 v0 v1 v5 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-neg
d_w'45'neg_888 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'neg_888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_w'45'neg_888 v11
du_w'45'neg_888 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'neg_888 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'neg_228 v1)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'neg_632 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-neg-float
d_w'45'neg'45'float_900 ::
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
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'neg'45'float_900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_w'45'neg'45'float_900
du_w'45'neg'45'float_900 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'neg'45'float_900
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'neg'45'float_236)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'neg'45'float_640)
-- Once.TypeCheck.Witness._.w-let
d_w'45'let_928 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'let_928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
               ~v12 ~v13 ~v14 v15 v16 ~v17 v18 v19
  = du_w'45'let_928 v11 v15 v16 v18 v19
du_w'45'let_928 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'let_928 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'let_254 v0 v5 v7)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'let_666 v1 v2 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-case
d_w'45'case_976 ::
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
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'case_976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 v22 v23 ~v24 ~v25
                v26 v27 v28 v29
  = du_w'45'case_976 v13 v14 v21 v22 v23 v26 v27 v28 v29
du_w'45'case_976 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'case_976 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'case_286 v0 v1 v9 v11
                              v13 v8)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Use.C_u'45'case_712 v2 v3 v4 v10 v12
                              v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-arith
d_w'45'arith_1012 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_IntArith_78 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'arith_1012 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 v14 v15 v16 v17 v18
  = du_w'45'arith_1012 v14 v15 v16 v17 v18
du_w'45'arith_1012 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_IntArith_78 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'arith_1012 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'arith_300 v2 v5 v7)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'arith_736 v0 v1 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-arith-float
d_w'45'arith'45'float_1040 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'arith'45'float_1040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_w'45'arith'45'float_1040 v14 v15 v16 v17 v18
du_w'45'arith'45'float_1040 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'arith'45'float_1040 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'arith'45'float_314 v2
                       v5 v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'arith'45'float_760 v0 v1 v6
                       v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-arith-float-il
d_w'45'arith'45'float'45'il_1068 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'arith'45'float'45'il_1068 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_w'45'arith'45'float'45'il_1068 v14 v15 v16 v17 v18
du_w'45'arith'45'float'45'il_1068 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'arith'45'float'45'il_1068 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'arith'45'float'45'il_328
                       v2 v5 v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'arith'45'float'45'il_784 v0
                       v1 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-arith-float-ir
d_w'45'arith'45'float'45'ir_1096 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'arith'45'float'45'ir_1096 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_w'45'arith'45'float'45'ir_1096 v14 v15 v16 v17 v18
du_w'45'arith'45'float'45'ir_1096 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_FloatArith_90 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'arith'45'float'45'ir_1096 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'arith'45'float'45'ir_342
                       v2 v5 v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'arith'45'float'45'ir_808 v0
                       v1 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-compare
d_w'45'compare_1124 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Compare_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'compare_1124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_w'45'compare_1124 v14 v15 v16 v17 v18
du_w'45'compare_1124 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Typing.T_Compare_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'compare_1124 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'compare_356 v2 v5 v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'compare_832 v0 v1 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-id-app
d_w'45'id'45'app_1144 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'id'45'app_1144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11 v12
  = du_w'45'id'45'app_1144 v11 v12
du_w'45'id'45'app_1144 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'id'45'app_1144 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'id'45'app_364 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'id'45'app_844 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-fst-app
d_w'45'fst'45'app_1160 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'fst'45'app_1160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 v12 v13
  = du_w'45'fst'45'app_1160 v12 v13
du_w'45'fst'45'app_1160 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'fst'45'app_1160 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'fst'45'app_374 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'fst'45'app_858 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-snd-app
d_w'45'snd'45'app_1176 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'snd'45'app_1176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 v12 v13
  = du_w'45'snd'45'app_1176 v12 v13
du_w'45'snd'45'app_1176 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'snd'45'app_1176 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'snd'45'app_384 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'snd'45'app_872 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-terminal-app
d_w'45'terminal'45'app_1190 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'terminal'45'app_1190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 v11 v12
  = du_w'45'terminal'45'app_1190 v11 v12
du_w'45'terminal'45'app_1190 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'terminal'45'app_1190 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'terminal'45'app_392
                v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Use.C_u'45'terminal'45'app_884 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-apply-app
d_w'45'apply'45'app_1206 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'apply'45'app_1206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13
  = du_w'45'apply'45'app_1206 v12 v13
du_w'45'apply'45'app_1206 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'apply'45'app_1206 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'apply'45'app_402 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'apply'45'app_898 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-apply-eff-app
d_w'45'apply'45'eff'45'app_1224 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'apply'45'eff'45'app_1224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 v13 v14 v15
  = du_w'45'apply'45'eff'45'app_1224 v13 v14 v15
du_w'45'apply'45'eff'45'app_1224 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'apply'45'eff'45'app_1224 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'apply'45'eff'45'app_414
                v1 v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Use.C_u'45'apply'45'eff'45'app_916 v0
                v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-Out-app
d_w'45'Out'45'app_1240 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'Out'45'app_1240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       v11 v12 v13
  = du_w'45'Out'45'app_1240 v11 v12 v13
du_w'45'Out'45'app_1240 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'Out'45'app_1240 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'Out'45'app_422 v1 v3)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'Out'45'app_930 v0 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-Out-act-app
d_w'45'Out'45'act'45'app_1256 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'Out'45'act'45'app_1256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 v11 v12 v13
  = du_w'45'Out'45'act'45'app_1256 v11 v12 v13
du_w'45'Out'45'act'45'app_1256 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'Out'45'act'45'app_1256 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'Out'45'act'45'app_430
                v1 v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Use.C_u'45'Out'45'act'45'app_944 v0 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-app
d_w'45'app_1282 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  (MAlonzo.Code.Once.Spec.Surface.Typing.T_SpecialHead_116 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'app_1282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                v12 ~v13 ~v14 v15 v16 ~v17 v18 v19
  = du_w'45'app_1282 v10 v12 v15 v16 v18 v19
du_w'45'app_1282 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'app_1282 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'app_446 v0 v1 v6 v8)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'app_970 v2 v3 v7 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-effApp
d_w'45'effApp_1312 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  (MAlonzo.Code.Once.Spec.Surface.Typing.T_SpecialHead_116 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'effApp_1312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                   ~v12 v13 v14 v15 v16 ~v17 v18 v19 v20
  = du_w'45'effApp_1312 v10 v13 v14 v15 v16 v18 v19 v20
du_w'45'effApp_1312 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'effApp_1312 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'effApp_462 v0 v1 v2 v5
                       v8 v10)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'effApp_998 v3 v4 v9 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-app-spine
d_w'45'app'45'spine_1342 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  (MAlonzo.Code.Once.Spec.Surface.Typing.T_SpecialHead_116 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'app'45'spine_1342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         v10 ~v11 ~v12 ~v13 v14 v15 ~v16 v17 v18
  = du_w'45'app'45'spine_1342 v10 v14 v15 v17 v18
du_w'45'app'45'spine_1342 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'app'45'spine_1342 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_s'45'app'45'spine_476 v0 v5
                       v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'app'45'spine_1022 v1 v2 v6
                       v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-id
d_w'45'id_1358 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'id_1358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_w'45'id_1358
du_w'45'id_1358 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'id_1358
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'id_486)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'id_1032)
-- Once.TypeCheck.Witness._.w-fst
d_w'45'fst_1366 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'fst_1366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'fst_1366
du_w'45'fst_1366 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'fst_1366
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'fst_494)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'fst_1040)
-- Once.TypeCheck.Witness._.w-snd
d_w'45'snd_1374 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'snd_1374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'snd_1374
du_w'45'snd_1374 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'snd_1374
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'snd_502)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'snd_1048)
-- Once.TypeCheck.Witness._.w-terminal
d_w'45'terminal_1380 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'terminal_1380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_w'45'terminal_1380
du_w'45'terminal_1380 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'terminal_1380
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'terminal_508)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'terminal_1054)
-- Once.TypeCheck.Witness._.w-initial
d_w'45'initial_1386 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'initial_1386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_w'45'initial_1386
du_w'45'initial_1386 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'initial_1386
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'initial_514)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'initial_1060)
-- Once.TypeCheck.Witness._.w-inl
d_w'45'inl_1394 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'inl_1394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'inl_1394
du_w'45'inl_1394 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'inl_1394
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'inl_522)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'inl_1068)
-- Once.TypeCheck.Witness._.w-inr
d_w'45'inr_1402 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'inr_1402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'inr_1402
du_w'45'inr_1402 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'inr_1402
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'inr_530)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'inr_1076)
-- Once.TypeCheck.Witness._.w-compose-g
d_w'45'compose'45'g_1424 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'compose'45'g_1424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 v19
  = du_w'45'compose'45'g_1424 v11 v15 v16 v17 v18 v19
du_w'45'compose'45'g_1424 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'compose'45'g_1424 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'compose'45'g_548 v0 v1
                       v6 v8)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'compose'45'g_1102 v2 v3 v7
                       v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-compose-f
d_w'45'compose'45'f_1458 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'compose'45'f_1458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22
  = du_w'45'compose'45'f_1458 v17 v18 v19 v20 v21 v22
du_w'45'compose'45'f_1458 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'compose'45'f_1458 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'compose'45'f_570 v0 v6
                       v4 v8)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'compose'45'f_1134 v1 v2 v7
                       v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-case′
d_w'45'case'8242'_1490 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'case'8242'_1490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 v19
  = du_w'45'case'8242'_1490 v15 v16 v17 v18 v19
du_w'45'case'8242'_1490 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'case'8242'_1490 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'case_588 v0 v5 v7)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'case_1160 v1 v2 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-pair′
d_w'45'pair'8242'_1520 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'pair'8242'_1520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 v19
  = du_w'45'pair'8242'_1520 v15 v16 v17 v18 v19
du_w'45'pair'8242'_1520 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'pair'8242'_1520 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'pair_606 v0 v5 v7)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'pair_1186 v1 v2 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-curry
d_w'45'curry_1546 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'curry_1546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 v16
  = du_w'45'curry_1546 v16
du_w'45'curry_1546 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'curry_1546 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'curry_622 v1)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'curry_1206 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-cata
d_w'45'cata_1564 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'cata_1564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 v15
  = du_w'45'cata_1564 v13 v14 v15
du_w'45'cata_1564 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'cata_1564 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'cata_634 v1 v3)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'cata_1224 v0 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-ana
d_w'45'ana_1586 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'ana_1586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13 v14 v15 v16 v17
  = du_w'45'ana_1586 v13 v14 v15 v16 v17
du_w'45'ana_1586 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'ana_1586 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'ana_648 v0 v2 v3 v5)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'ana_1246 v1 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-loop
d_w'45'loop_1606 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'loop_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13
  = du_w'45'loop_1606 v12 v13
du_w'45'loop_1606 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'loop_1606 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'loop_658 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'loop_1260 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-sub
d_w'45'sub_1622 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'sub_1622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13 v14
  = du_w'45'sub_1622 v13 v14
du_w'45'sub_1622 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'sub_1622 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'sub_668 v2 v1)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'sub_1276 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-lam
d_w'45'lam_1648 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'lam_1648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13 ~v14 ~v15 ~v16 ~v17 v18
  = du_w'45'lam_1648 v13 v18
du_w'45'lam_1648 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'lam_1648 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'lam_684 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'lam_1298 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-pair-lit
d_w'45'pair'45'lit_1672 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'pair'45'lit_1672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17
  = du_w'45'pair'45'lit_1672 v14 v15 v16 v17
du_w'45'pair'45'lit_1672 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'pair'45'lit_1672 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'pair'45'lit_698 v4 v6)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'pair'45'lit_1320 v0 v1 v5
                       v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-In-app
d_w'45'In'45'app_1690 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'In'45'app_1690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11 v12 v13
  = du_w'45'In'45'app_1690 v11 v12 v13
du_w'45'In'45'app_1690 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'In'45'app_1690 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'In'45'app_706 v1 v3)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'In'45'app_1334 v0 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-apply-app′
d_w'45'apply'45'app'8242'_1708 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'apply'45'app'8242'_1708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12 v13
  = du_w'45'apply'45'app'8242'_1708 v12 v13
du_w'45'apply'45'app'8242'_1708 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'apply'45'app'8242'_1708 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'apply'45'app_716 v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Use.C_u'45'apply'45'app_1348 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-inl-app
d_w'45'inl'45'app_1724 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'inl'45'app_1724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 v12 v13
  = du_w'45'inl'45'app_1724 v12 v13
du_w'45'inl'45'app_1724 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'inl'45'app_1724 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'inl'45'app_726 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'inl'45'app_1362 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-inr-app
d_w'45'inr'45'app_1740 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'inr'45'app_1740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 v12 v13
  = du_w'45'inr'45'app_1740 v12 v13
du_w'45'inr'45'app_1740 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'inr'45'app_1740 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'inr'45'app_736 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'inr'45'app_1376 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-initial-app
d_w'45'initial'45'app_1754 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'initial'45'app_1754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11 v12
  = du_w'45'initial'45'app_1754 v11 v12
du_w'45'initial'45'app_1754 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'initial'45'app_1754 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'initial'45'app_744 v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Use.C_u'45'initial'45'app_1388 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-poly
d_w'45'poly_1766 ::
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'poly_1766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 v13
  = du_w'45'poly_1766 v11 v13
du_w'45'poly_1766 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'poly_1766 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_c'45'poly_752 v0 v1)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'poly_1402)
-- Once.TypeCheck.Witness._.w-infer
d_w'45'infer_1794 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'infer_1794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 v16 v17 v18
  = du_w'45'infer_1794 v16 v17 v18
du_w'45'infer_1794 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'infer_1794 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'infer_772 v3 v1 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'infer_1430 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-poly↦
d_w'45'poly'8614'_1824 ::
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Occurs_240 ->
   MAlonzo.Code.Once.Spec.Type.T_Occurs_240) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'poly'8614'_1824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       v11 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 v24
  = du_w'45'poly'8614'_1824 v11 v12 v13 v19 v21 v24
du_w'45'poly'8614'_1824 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Occurs_240 ->
   MAlonzo.Code.Once.Spec.Type.T_Occurs_240) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'poly'8614'_1824 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'poly_794 v0 v1 v2 v3
         v4 v5)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'poly_1466)
-- Once.TypeCheck.Witness._.w-lam↦
d_w'45'lam'8614'_1862 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'lam'8614'_1862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      ~v11 ~v12 ~v13 v14 ~v15 v16
  = du_w'45'lam'8614'_1862 v14 v16
du_w'45'lam'8614'_1862 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'lam'8614'_1862 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'lam_808 v2)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'lam_1486 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-compose↦
d_w'45'compose'8614'_1888 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'compose'8614'_1888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 v19
  = du_w'45'compose'8614'_1888 v11 v15 v16 v17 v18 v19
du_w'45'compose'8614'_1888 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'compose'8614'_1888 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'compose_826 v0 v1 v6
                       v8)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Use.C_u'45'compose_1512 v2 v3 v7 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-id↦
d_w'45'id'8614'_1902 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'id'8614'_1902 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_w'45'id'8614'_1902
du_w'45'id'8614'_1902 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'id'8614'_1902
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'id_832)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'id_1518)
-- Once.TypeCheck.Witness._.w-fst↦
d_w'45'fst'8614'_1910 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'fst'8614'_1910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'fst'8614'_1910
du_w'45'fst'8614'_1910 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'fst'8614'_1910
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'fst_840)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'fst_1526)
-- Once.TypeCheck.Witness._.w-snd↦
d_w'45'snd'8614'_1918 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'snd'8614'_1918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_w'45'snd'8614'_1918
du_w'45'snd'8614'_1918 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'snd'8614'_1918
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'snd_848)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'snd_1534)
-- Once.TypeCheck.Witness._.w-terminal↦
d_w'45'terminal'8614'_1924 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'terminal'8614'_1924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_w'45'terminal'8614'_1924
du_w'45'terminal'8614'_1924 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'terminal'8614'_1924
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'terminal_854)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'terminal_1540)
-- Once.TypeCheck.Witness._.w-initial↦
d_w'45'initial'8614'_1928 ::
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
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'initial'8614'_1928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_w'45'initial'8614'_1928
du_w'45'initial'8614'_1928 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'initial'8614'_1928
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'initial_858)
      (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'initial_1544)
-- Once.TypeCheck.Witness._.w-case↦
d_w'45'case'8614'_1954 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'case'8614'_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22
  = du_w'45'case'8614'_1954 v17 v18 v19 v20 v21 v22
du_w'45'case'8614'_1954 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'case'8614'_1954 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'case_880 v0 v6 v8 v5)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'case_1576 v1 v2 v7 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-pair↦
d_w'45'pair'8614'_1986 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'pair'8614'_1986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 v19
  = du_w'45'pair'8614'_1986 v15 v16 v17 v18 v19
du_w'45'pair'8614'_1986 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'pair'8614'_1986 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'pair_898 v0 v5 v7)
                    (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'pair_1602 v1 v2 v6 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Witness._.w-cata↦
d_w'45'cata'8614'_2008 ::
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
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_w'45'cata'8614'_2008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 v13 v14 v15
  = du_w'45'cata'8614'_2008 v13 v14 v15
du_w'45'cata'8614'_2008 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_w'45'cata'8614'_2008 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Surface.Typing.C_d'45'cata_910 v1 v3)
             (coe MAlonzo.Code.Once.TypeCheck.Use.C_u'45'cata_1620 v0 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
