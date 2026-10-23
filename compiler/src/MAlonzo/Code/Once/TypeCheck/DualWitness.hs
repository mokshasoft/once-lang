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

module MAlonzo.Code.Once.TypeCheck.DualWitness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.TypeCheck.SpecWitness

-- Once.TypeCheck.DualWitness.DI
d_DI_10 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_DI_10 = erased
-- Once.TypeCheck.DualWitness.DC
d_DC_24 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_DC_24 = erased
-- Once.TypeCheck.DualWitness.DD
d_DD_38 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d_DD_38 = erased
-- Once.TypeCheck.DualWitness._._⇒⟨_⟩_
d__'8658''10216'_'10217'__60 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658''10216'_'10217'__60 ~v0 v1 v2 v3
  = du__'8658''10216'_'10217'__60 v1 v2 v3
du__'8658''10216'_'10217'__60 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du__'8658''10216'_'10217'__60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
      (coe v2)
-- Once.TypeCheck.DualWitness._.Z
d_Z_68 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d_Z_68 v0
  = coe
      MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
      (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
-- Once.TypeCheck.DualWitness._.gn
d_gn_70 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_gn_70 ~v0 v1 = du_gn_70 v1
du_gn_70 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
du_gn_70 v0
  = coe
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
      (coe
         MAlonzo.Code.Once.Spec.Name.C_canonical_12
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("Generators" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.TypeCheck.DualWitness._.dt-int
d_dt'45'int_76 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'int_76 ~v0 ~v1 v2 = du_dt'45'int_76 v2
du_dt'45'int_76 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'int_76 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38)
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'int_1128 (coe v0))
-- Once.TypeCheck.DualWitness._.dt-float
d_dt'45'float_86 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'float_86 ~v0 ~v1 v2 v3 v4 = du_dt'45'float_86 v2 v3 v4
du_dt'45'float_86 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'float_86 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'float_1702
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-unit
d_dt'45'unit_94 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'unit_94 ~v0 ~v1 = du_dt'45'unit_94
du_dt'45'unit_94 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'unit_94
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_52)
      (\ v0 v1 ->
         coe MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit_2274)
-- Once.TypeCheck.DualWitness._.dt-unit-var
d_dt'45'unit'45'var_96 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'unit'45'var_96 ~v0 ~v1 = du_dt'45'unit'45'var_96
du_dt'45'unit'45'var_96 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'unit'45'var_96
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_56)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit'45'var_2840)
-- Once.TypeCheck.DualWitness._.dt-var-local
d_dt'45'var'45'local_106 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'local_106 v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_dt'45'var'45'local_106 v0 v1 v2 v5
du_dt'45'var'45'local_106 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'local_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_68 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'local_3414
           (coe v0) (coe v1) (coe v2) (coe v3) v4)
-- Once.TypeCheck.DualWitness._.dt-var-resolved
d_dt'45'var'45'resolved_116 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'resolved_116 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9
  = du_dt'45'var'45'resolved_116 v2 v3 v5 v6 v8
du_dt'45'var'45'resolved_116 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'resolved_116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_78 v1 v2
         v3 v4)
      (\ v5 v6 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'resolved_3990
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) v5)
-- Once.TypeCheck.DualWitness._.dt-var-own
d_dt'45'var'45'own_136 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'own_136 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_dt'45'var'45'own_136 v2 v3
du_dt'45'var'45'own_136 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'own_136 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_88 v1)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'own_4584
           (coe v0) (coe v1) v2)
-- Once.TypeCheck.DualWitness._.dt-var-import
d_dt'45'var'45'import_150 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'import_150 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dt'45'var'45'import_150 v3 v8
du_dt'45'var'45'import_150 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'import_150 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'import_98 v0 v1)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'import_5166
           v3)
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate-infer
d_dt'45'var'45'poly'45'instantiate'45'infer_176 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'poly'45'instantiate'45'infer_176 ~v0 ~v1 v2 ~v3 v4
                                                v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_dt'45'var'45'poly'45'instantiate'45'infer_176
      v2 v4 v5 v6 v7 v11
du_dt'45'var'45'poly'45'instantiate'45'infer_176 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate'45'infer_176 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_114
         v1 v2 v3 v4 v5)
      (\ v6 v7 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate'45'infer_5750
           (coe v0) (coe v1) (coe v2) (coe v3) v6)
-- Once.TypeCheck.DualWitness._.dt-annot
d_dt'45'annot_198 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'annot_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_dt'45'annot_198 v6
du_dt'45'annot_198 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'annot_198 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_126
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'annot_6338
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-pair
d_dt'45'pair_216 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_dt'45'pair_216 v6 v7 v8 v9
du_dt'45'pair_216 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair_216 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_142 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair_6924 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-neg
d_dt'45'neg_226 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg_226 ~v0 ~v1 ~v2 ~v3 v4 = du_dt'45'neg_226 v4
du_dt'45'neg_226 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg_226 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_150
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg_7502
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-neg-float
d_dt'45'neg'45'float_236 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg'45'float_236 ~v0 ~v1 v2 v3 v4
  = du_dt'45'neg'45'float_236 v2 v3 v4
du_dt'45'neg'45'float_236 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg'45'float_236 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_160)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg'45'float_8078
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-let
d_dt'45'let_260 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'let_260 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_dt'45'let_260 v2 v5 v7 v8 v9 v10 v11
du_dt'45'let_260 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'let_260 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'let_180 v1 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'let_8666 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-case
d_dt'45'case_296 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'case_296 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20
  = du_dt'45'case_296
      v3 v5 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_dt'45'case_296 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'case_296 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case_214 v2 v3 v4 v5 v7 v8
         v9 v10 v11 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v13))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v14)) v15)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case_9276 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10) (coe v11)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v12))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v14)) (coe v15))
-- Once.TypeCheck.DualWitness._.dt-binop-arith
d_dt'45'binop'45'arith_316 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith_316 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_dt'45'binop'45'arith_316 v2 v5 v6 v8 v9
du_dt'45'binop'45'arith_316 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith_316 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith_9878
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float
d_dt'45'binop'45'arith'45'float_334 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float_334 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 v8
                                    v9
  = du_dt'45'binop'45'arith'45'float_334 v2 v5 v6 v8 v9
du_dt'45'binop'45'arith'45'float_334 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float_334 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float_10464
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-il
d_dt'45'binop'45'arith'45'float'45'il_352 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float'45'il_352 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 v8 v9
  = du_dt'45'binop'45'arith'45'float'45'il_352 v2 v5 v6 v8 v9
du_dt'45'binop'45'arith'45'float'45'il_352 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'il_352 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'il_11050
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-ir
d_dt'45'binop'45'arith'45'float'45'ir_370 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float'45'ir_370 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 v8 v9
  = du_dt'45'binop'45'arith'45'float'45'ir_370 v2 v5 v6 v8 v9
du_dt'45'binop'45'arith'45'float'45'ir_370 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'ir_370 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'ir_11636
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-cmp
d_dt'45'binop'45'cmp_388 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'cmp_388 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 v9
  = du_dt'45'binop'45'cmp_388 v2 v5 v6 v8 v9
du_dt'45'binop'45'cmp_388 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'cmp_388 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'cmp_12222
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-app
d_dt'45'id'45'app_402 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'app_402 ~v0 ~v1 ~v2 v3 v4 v5
  = du_dt'45'id'45'app_402 v3 v4 v5
du_dt'45'id'45'app_402 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'app_402 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_294 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'app_12804
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-fst-app
d_dt'45'fst'45'app_414 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'app_414 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'fst'45'app_414 v3 v4 v5 v6
du_dt'45'fst'45'app_414 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'app_414 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_306 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'app_13382
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-snd-app
d_dt'45'snd'45'app_426 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'app_426 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'snd'45'app_426 v3 v4 v5 v6
du_dt'45'snd'45'app_426 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'app_426 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_318 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'app_13960
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-terminal-app
d_dt'45'terminal'45'app_436 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'app_436 ~v0 ~v1 ~v2 v3 v4 v5
  = du_dt'45'terminal'45'app_436 v3 v4 v5
du_dt'45'terminal'45'app_436 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'app_436 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_328 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'app_14536
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-apply-app-infer
d_dt'45'apply'45'app'45'infer_448 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'app'45'infer_448 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'apply'45'app'45'infer_448 v3 v4 v5 v6
du_dt'45'apply'45'app'45'infer_448 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'app'45'infer_448 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_340
         v0 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'app'45'infer_15114
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-eff-app-infer
d_dt'45'apply'45'eff'45'app'45'infer_464 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'eff'45'app'45'infer_464 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
                                         v8
  = du_dt'45'apply'45'eff'45'app'45'infer_464 v3 v4 v5 v6 v7 v8
du_dt'45'apply'45'eff'45'app'45'infer_464 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'eff'45'app'45'infer_464 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_356
         v0 v2 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'eff'45'app'45'infer_15696
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-Out-app-infer
d_dt'45'Out'45'app'45'infer_478 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'Out'45'app'45'infer_478 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 v8
  = du_dt'45'Out'45'app'45'infer_478 v3 v5 v6 v8
du_dt'45'Out'45'app'45'infer_478 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'app'45'infer_478 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_368 v0
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'app'45'infer_16276
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-Out-eff-app-infer
d_dt'45'Out'45'eff'45'app'45'infer_494 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'Out'45'eff'45'app'45'infer_494 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7
                                       v8
  = du_dt'45'Out'45'eff'45'app'45'infer_494 v3 v5 v6 v8
du_dt'45'Out'45'eff'45'app'45'infer_494 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'eff'45'app'45'infer_494 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_380
         v0 v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'eff'45'app'45'infer_16858
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-app
d_dt'45'app_516 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'app_516 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_dt'45'app_516 v4 v6 v7 v8 v10 v11
du_dt'45'app_516 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app_516 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app_398 v0 v1 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app_17450 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-effApp
d_dt'45'effApp_540 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'effApp_540 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_dt'45'effApp_540 v4 v6 v7 v8 v9 v11 v12
du_dt'45'effApp_540 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'effApp_540 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_418 v0 v1 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'effApp_18042
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-app-spine
d_dt'45'app'45'spine_562 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'app'45'spine_562 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 v10
  = du_dt'45'app'45'spine_562 v4 v6 v7 v9 v10
du_dt'45'app'45'spine_562 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app'45'spine_562 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_434 v0 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app'45'spine_18632
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-check
d_dt'45'id'45'check_576 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'check_576 ~v0 ~v1 v2 v3 v4
  = du_dt'45'id'45'check_576 v2 v3 v4
du_dt'45'id'45'check_576 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'check_576 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_446 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'check_19236
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-fst-check
d_dt'45'fst'45'check_588 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'check_588 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'fst'45'check_588 v2 v3 v4 v5
du_dt'45'fst'45'check_588 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'check_588 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_458 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'check_19810
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-snd-check
d_dt'45'snd'45'check_600 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'check_600 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'snd'45'check_600 v2 v3 v4 v5
du_dt'45'snd'45'check_600 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'check_600 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_470 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'check_20384
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-terminal-morph-check
d_dt'45'terminal'45'morph'45'check_610 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'morph'45'check_610 ~v0 ~v1 v2 v3 v4
  = du_dt'45'terminal'45'morph'45'check_610 v2 v3 v4
du_dt'45'terminal'45'morph'45'check_610 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'morph'45'check_610 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_480
         v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'morph'45'check_20956
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-initial-morph-check
d_dt'45'initial'45'morph'45'check_620 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'morph'45'check_620 ~v0 ~v1 v2 v3 v4
  = du_dt'45'initial'45'morph'45'check_620 v2 v3 v4
du_dt'45'initial'45'morph'45'check_620 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'morph'45'check_620 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_490
         v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'morph'45'check_21528
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-inl-morph-check
d_dt'45'inl'45'morph'45'check_632 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'morph'45'check_632 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inl'45'morph'45'check_632 v2 v3 v4 v5
du_dt'45'inl'45'morph'45'check_632 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'morph'45'check_632 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_502
         v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'morph'45'check_22102
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-inr-morph-check
d_dt'45'inr'45'morph'45'check_644 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'morph'45'check_644 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inr'45'morph'45'check_644 v2 v3 v4 v5
du_dt'45'inr'45'morph'45'check_644 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'morph'45'check_644 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_514
         v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'morph'45'check_22676
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-compose-check-g
d_dt'45'compose'45'check'45'g_664 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'compose'45'check'45'g_664 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                  v9 v10 v11
  = du_dt'45'compose'45'check'45'g_664 v4 v5 v7 v8 v9 v10 v11
du_dt'45'compose'45'check'45'g_664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'compose'45'check'45'g_664 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_534
         v1 v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'g_23258
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-compose-check-f
d_dt'45'compose'45'check'45'f_692 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'compose'45'check'45'f_692 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 v12 v13 v14
  = du_dt'45'compose'45'check'45'f_692
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_dt'45'compose'45'check'45'f_692 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'compose'45'check'45'f_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_558
         v1 v3 v5 v6 v7 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         v9 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'f_23852
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe v9) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
-- Once.TypeCheck.DualWitness._.dt-case-copair-check
d_dt'45'case'45'copair'45'check_718 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'case'45'copair'45'check_718 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                    v9 v10 v11
  = du_dt'45'case'45'copair'45'check_718 v4 v5 v7 v8 v9 v10 v11
du_dt'45'case'45'copair'45'check_718 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'case'45'copair'45'check_718 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_578
         v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case'45'copair'45'check_24444
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-morph-check
d_dt'45'pair'45'morph'45'check_742 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair'45'morph'45'check_742 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
                                   v9 v10 v11
  = du_dt'45'pair'45'morph'45'check_742 v4 v7 v8 v9 v10 v11
du_dt'45'pair'45'morph'45'check_742 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'morph'45'check_742 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_598
         v2 v3 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'morph'45'check_25034
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-curry-check
d_dt'45'curry'45'check_766 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'curry'45'check_766 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 ~v8 v9 v10
  = du_dt'45'curry'45'check_766 v3 v4 v6 v7 v9 v10
du_dt'45'curry'45'check_766 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'curry'45'check_766 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_618 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'curry'45'check_25624
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-cata-check
d_dt'45'cata'45'check_784 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'cata'45'check_784 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_dt'45'cata'45'check_784 v3 v5 v6 v7 v8 v9
du_dt'45'cata'45'check_784 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'cata'45'check_784 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_634 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'cata'45'check_26206
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-ana-check
d_dt'45'ana'45'check_808 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'ana'45'check_808 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_dt'45'ana'45'check_808 v3 v4 v5 v7 v8 v9 v10 v11
du_dt'45'ana'45'check_808 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'ana'45'check_808 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_654 v3 v4 v5
         v6 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'ana'45'check_26794
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
-- Once.TypeCheck.DualWitness._.dt-loop-check
d_dt'45'loop'45'check_826 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'loop'45'check_826 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_dt'45'loop'45'check_826 v3 v5 v6
du_dt'45'loop'45'check_826 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'loop'45'check_826 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_666 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'loop'45'check_27376
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-sub
d_dt'45'sub_838 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'sub_838 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_dt'45'sub_838 v3 v4 v6 v7
du_dt'45'sub_838 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'sub_838 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'sub_27954 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe v3))
-- Once.TypeCheck.DualWitness._.dt-lam
d_dt'45'lam_862 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'lam_862 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 ~v11 v12
  = du_dt'45'lam_862 v2 v4 v6 v7 v8 v10 v12
du_dt'45'lam_862 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'lam_862 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_700 v3 v5
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'lam_28544 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-lit-check
d_dt'45'pair'45'lit'45'check_882 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair'45'lit'45'check_882 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                 v9
  = du_dt'45'pair'45'lit'45'check_882 v6 v7 v8 v9
du_dt'45'pair'45'lit'45'check_882 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'lit'45'check_882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_716
         v0 v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'lit'45'check_29132
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-In-app-check
d_dt'45'In'45'app'45'check_894 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'In'45'app'45'check_894 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'In'45'app'45'check_894 v3 v4 v5 v6
du_dt'45'In'45'app'45'check_894 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'In'45'app'45'check_894 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_726 v1
         v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'In'45'app'45'check_29712
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-check
d_dt'45'apply'45'check_908 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'check_908 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'apply'45'check_908 v3 v4 v5 v6
du_dt'45'apply'45'check_908 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'check_908 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_738 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'check_30292
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inl-app-check
d_dt'45'inl'45'app'45'check_920 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'app'45'check_920 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'inl'45'app'45'check_920 v3 v4 v5 v6
du_dt'45'inl'45'app'45'check_920 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'app'45'check_920 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_750 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'app'45'check_30870
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inr-app-check
d_dt'45'inr'45'app'45'check_932 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'app'45'check_932 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_dt'45'inr'45'app'45'check_932 v3 v4 v5 v6
du_dt'45'inr'45'app'45'check_932 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'app'45'check_932 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_762 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'app'45'check_31448
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-initial-app-check
d_dt'45'initial'45'app'45'check_942 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'app'45'check_942 ~v0 ~v1 ~v2 v3 v4 v5
  = du_dt'45'initial'45'app'45'check_942 v3 v4 v5
du_dt'45'initial'45'app'45'check_942 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'app'45'check_942 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_772
         v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'app'45'check_32024
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate
d_dt'45'var'45'poly'45'instantiate_958 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'poly'45'instantiate_958 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
                                       ~v8 ~v9 ~v10 v11
  = du_dt'45'var'45'poly'45'instantiate_958 v2 v4 v5 v6 v11
du_dt'45'var'45'poly'45'instantiate_958 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate_958 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_786
         v1 v2 v3 v4)
      (\ v5 v6 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate_32606
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) v5)
-- Once.TypeCheck.DualWitness._.dd-infer
d_dd'45'infer_984 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'infer_984 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_dd'45'infer_984 v3 v4 v5 v6 v7 v9 v10 v11
du_dd'45'infer_984 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'infer_984 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_806 v1 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)) v6 v7)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'infer_33214
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)) (coe v6)
         (coe v7))
-- Once.TypeCheck.DualWitness._.dd-poly
d_dd'45'poly_1016 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'poly_1016 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                  ~v14 ~v15 v16 v17 v18 v19
  = du_dd'45'poly_1016
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v19
du_dd'45'poly_1016 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'poly_1016 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_830 v4 v5 v6 v7 v8 v9
         v10 v11 v12 v13)
      (\ v14 v15 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'poly_33810
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
           (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
           v14)
-- Once.TypeCheck.DualWitness._.dd-lam
d_dd'45'lam_1050 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'lam_1050 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 v10
  = du_dd'45'lam_1050 v2 v4 v6 v7 v9 v10
du_dd'45'lam_1050 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'lam_1050 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_850 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'lam_34416 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-compose
d_dd'45'compose_1072 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'compose_1072 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_dd'45'compose_1072 v4 v5 v7 v8 v9 v10 v11
du_dd'45'compose_1072 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'compose_1072 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_870 v1 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'compose_35006
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dd-id
d_dd'45'id_1086 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'id_1086 ~v0 ~v1 v2 v3 v4 = du_dd'45'id_1086 v2 v3 v4
du_dd'45'id_1086 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'id_1086 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'id_880 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'id_35586 (coe v0)
           (coe v1))
-- Once.TypeCheck.DualWitness._.dd-fst
d_dd'45'fst_1098 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'fst_1098 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'fst_1098 v2 v3 v4 v5
du_dd'45'fst_1098 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'fst_1098 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_892 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'fst_36160 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-snd
d_dd'45'snd_1110 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'snd_1110 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'snd_1110 v2 v3 v4 v5
du_dd'45'snd_1110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'snd_1110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_904 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'snd_36734 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-terminal
d_dd'45'terminal_1120 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'terminal_1120 ~v0 ~v1 v2 v3 v4
  = du_dd'45'terminal_1120 v2 v3 v4
du_dd'45'terminal_1120 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'terminal_1120 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_914 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'terminal_37306
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dd-initial
d_dd'45'initial_1128 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'initial_1128 ~v0 ~v1 v2 v3 = du_dd'45'initial_1128 v2 v3
du_dd'45'initial_1128 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'initial_1128 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_922 v1)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'initial_37876
           (coe v0))
-- Once.TypeCheck.DualWitness._.dd-case
d_dd'45'case_1152 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'case_1152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                  v14
  = du_dd'45'case_1152 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_dd'45'case_1152 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'case_1152 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'case_946 v2 v3 v6 v7
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)) v10)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'case_38462
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)) (coe v10))
-- Once.TypeCheck.DualWitness._.dd-pair
d_dd'45'pair_1178 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'pair_1178 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_dd'45'pair_1178 v4 v7 v8 v9 v10 v11
du_dd'45'pair_1178 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'pair_1178 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_966 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'pair_39054
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-cata
d_dd'45'cata_1198 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'cata_1198 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_dd'45'cata_1198 v3 v5 v6 v7 v8 v9
du_dd'45'cata_1198 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'cata_1198 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_982 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'cata_39640
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
