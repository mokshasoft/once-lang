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
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.TypeCheck.SpecWitness

-- Once.TypeCheck.DualWitness.DI
d_DI_14 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> ()
d_DI_14 = erased
-- Once.TypeCheck.DualWitness.DC
d_DC_34 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> ()
d_DC_34 = erased
-- Once.TypeCheck.DualWitness.DD
d_DD_58 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> ()
d_DD_58 = erased
-- Once.TypeCheck.DualWitness._._⇒⟨_⟩_
d__'8658''10216'_'10217'__82 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658''10216'_'10217'__82 ~v0 v1 v2 v3
  = du__'8658''10216'_'10217'__82 v1 v2 v3
du__'8658''10216'_'10217'__82 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du__'8658''10216'_'10217'__82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
      (coe v2)
-- Once.TypeCheck.DualWitness._.Z
d_Z_90 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d_Z_90 v0
  = coe
      MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
      (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
-- Once.TypeCheck.DualWitness._.gn
d_gn_92 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_gn_92 ~v0 v1 = du_gn_92 v1
du_gn_92 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
du_gn_92 v0
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
-- Once.TypeCheck.DualWitness._.E
d_E_96 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_E_96 = erased
-- Once.TypeCheck.DualWitness._.dt-int
d_dt'45'int_100 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'int_100 ~v0 ~v1 v2 = du_dt'45'int_100 v2
du_dt'45'int_100 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'int_100 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38)
      (\ v1 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'int_2462 (coe v0))
-- Once.TypeCheck.DualWitness._.dt-float
d_dt'45'float_110 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'float_110 ~v0 ~v1 v2 v3 v4 = du_dt'45'float_110 v2 v3 v4
du_dt'45'float_110 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'float_110 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'float_3058
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-unit
d_dt'45'unit_118 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'unit_118 ~v0 ~v1 = du_dt'45'unit_118
du_dt'45'unit_118 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'unit_118
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_52)
      (\ v0 ->
         coe MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit_3652)
-- Once.TypeCheck.DualWitness._.dt-unit-var
d_dt'45'unit'45'var_120 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'unit'45'var_120 ~v0 ~v1 = du_dt'45'unit'45'var_120
du_dt'45'unit'45'var_120 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'unit'45'var_120
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_56)
      (\ v0 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit'45'var_4240)
-- Once.TypeCheck.DualWitness._.dt-var-local
d_dt'45'var'45'local_130 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'local_130 v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_dt'45'var'45'local_130 v0 v1 v2 v5
du_dt'45'var'45'local_130 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'local_130 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_68 v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'local_4836
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.TypeCheck.DualWitness._.dt-var-resolved
d_dt'45'var'45'resolved_144 ::
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
d_dt'45'var'45'resolved_144 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9
  = du_dt'45'var'45'resolved_144 v2 v3 v5 v6 v8
du_dt'45'var'45'resolved_144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'resolved_144 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_78 v1 v2
         v3 v4)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'resolved_5438
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.TypeCheck.DualWitness._.dt-var-own
d_dt'45'var'45'own_166 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'var'45'own_166 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_dt'45'var'45'own_166 v2 v3
du_dt'45'var'45'own_166 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'own_166 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_88 v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'own_6058
         (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate-infer
d_dt'45'var'45'poly'45'instantiate'45'infer_188 ::
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
d_dt'45'var'45'poly'45'instantiate'45'infer_188 ~v0 ~v1 v2 ~v3 v4
                                                v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_dt'45'var'45'poly'45'instantiate'45'infer_188
      v2 v4 v5 v6 v7 v11
du_dt'45'var'45'poly'45'instantiate'45'infer_188 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate'45'infer_188 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_104
         v1 v2 v3 v4 v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate'45'infer_6672
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.TypeCheck.DualWitness._.dt-annot
d_dt'45'annot_212 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'annot_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_dt'45'annot_212 v7
du_dt'45'annot_212 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'annot_212 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_116
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'annot_7290
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-pair
d_dt'45'pair_234 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_dt'45'pair_234 v6 v7 v10 v11
du_dt'45'pair_234 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair_234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_132 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair_7918 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-neg
d_dt'45'neg_246 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg_246 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_dt'45'neg_246 v5
du_dt'45'neg_246 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg_246 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_140
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg_8524
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-neg-float
d_dt'45'neg'45'float_256 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg'45'float_256 ~v0 ~v1 v2 v3 v4
  = du_dt'45'neg'45'float_256 v2 v3 v4
du_dt'45'neg'45'float_256 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg'45'float_256 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_150)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg'45'float_9124
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-let
d_dt'45'let_284 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'let_284 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
                v13
  = du_dt'45'let_284 v2 v5 v7 v8 v9 v12 v13
du_dt'45'let_284 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'let_284 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'let_170 v1 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'let_9738 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-case
d_dt'45'case_328 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'case_328 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 ~v17 ~v18 ~v19 v20 v21 v22 v23
  = du_dt'45'case_328
      v3 v5 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v20 v21 v22 v23
du_dt'45'case_328 ::
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
du_dt'45'case_328 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case_204 v2 v3 v4 v5 v7 v8
         v9 v10 v11 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v13))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v14)) v15)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case_10382
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v12))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v14)) (coe v15))
-- Once.TypeCheck.DualWitness._.dt-binop-arith
d_dt'45'binop'45'arith_354 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith_354 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
                           v11
  = du_dt'45'binop'45'arith_354 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith_354 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith_354 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_218 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith_11024
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float
d_dt'45'binop'45'arith'45'float_378 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float_378 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7
                                    ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float_378 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float_378 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float_378 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_232
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float_11644
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-il
d_dt'45'binop'45'arith'45'float'45'il_402 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float'45'il_402 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float'45'il_402 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float'45'il_402 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'il_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_246
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'il_12264
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-ir
d_dt'45'binop'45'arith'45'float'45'ir_426 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'arith'45'float'45'ir_426 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float'45'ir_426 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float'45'ir_426 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'ir_426 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_260
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'ir_12888
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-cmp
d_dt'45'binop'45'cmp_450 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'binop'45'cmp_450 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
                         v11
  = du_dt'45'binop'45'cmp_450 v2 v5 v6 v10 v11
du_dt'45'binop'45'cmp_450 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'cmp_450 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_274 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'cmp_13512
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-app
d_dt'45'id'45'app_466 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'app_466 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'id'45'app_466 v3 v4 v6
du_dt'45'id'45'app_466 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'app_466 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_284 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'app_14124
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-fst-app
d_dt'45'fst'45'app_480 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'app_480 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'fst'45'app_480 v3 v4 v5 v7
du_dt'45'fst'45'app_480 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'app_480 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_296 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'app_14728
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-snd-app
d_dt'45'snd'45'app_494 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'app_494 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'snd'45'app_494 v3 v4 v5 v7
du_dt'45'snd'45'app_494 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'app_494 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_308 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'app_15332
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-terminal-app
d_dt'45'terminal'45'app_506 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'app_506 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'terminal'45'app_506 v3 v4 v6
du_dt'45'terminal'45'app_506 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'app_506 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_318 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'app_15934
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-apply-app-infer
d_dt'45'apply'45'app'45'infer_520 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'app'45'infer_520 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'apply'45'app'45'infer_520 v3 v4 v5 v7
du_dt'45'apply'45'app'45'infer_520 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'app'45'infer_520 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_330
         v0 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'app'45'infer_16538
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-eff-app-infer
d_dt'45'apply'45'eff'45'app'45'infer_538 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'eff'45'app'45'infer_538 ~v0 ~v1 ~v2 v3 v4 v5 v6
                                         ~v7 v8 v9
  = du_dt'45'apply'45'eff'45'app'45'infer_538 v3 v4 v5 v6 v8 v9
du_dt'45'apply'45'eff'45'app'45'infer_538 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'eff'45'app'45'infer_538 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_346
         v0 v2 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'eff'45'app'45'infer_17146
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-Out-app-infer
d_dt'45'Out'45'app'45'infer_560 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'Out'45'app'45'infer_560 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9
  = du_dt'45'Out'45'app'45'infer_560 v3 v5 v7 v9
du_dt'45'Out'45'app'45'infer_560 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'app'45'infer_560 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_358 v0
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'app'45'infer_17758
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-Out-eff-app-infer
d_dt'45'Out'45'eff'45'app'45'infer_586 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'Out'45'eff'45'app'45'infer_586 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
                                       ~v8 v9
  = du_dt'45'Out'45'eff'45'app'45'infer_586 v3 v5 v7 v9
du_dt'45'Out'45'eff'45'app'45'infer_586 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'eff'45'app'45'infer_586 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_370
         v0 v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'eff'45'app'45'infer_18376
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-app
d_dt'45'app_612 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'app_612 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 v12
                v13
  = du_dt'45'app_612 v4 v6 v7 v8 v12 v13
du_dt'45'app_612 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app_612 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app_388 v0 v1 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app_18994 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-effApp
d_dt'45'effApp_640 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'effApp_640 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 v11
                   ~v12 v13 v14
  = du_dt'45'effApp_640 v4 v6 v7 v8 v11 v13 v14
du_dt'45'effApp_640 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'effApp_640 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_408 v0 v1 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'effApp_19616
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-app-spine
d_dt'45'app'45'spine_666 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'app'45'spine_666 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                         v11 v12
  = du_dt'45'app'45'spine_666 v4 v6 v7 v11 v12
du_dt'45'app'45'spine_666 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app'45'spine_666 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_424 v0 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app'45'spine_20236
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-check
d_dt'45'id'45'check_680 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'check_680 ~v0 ~v1 v2 v3 v4
  = du_dt'45'id'45'check_680 v2 v3 v4
du_dt'45'id'45'check_680 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'check_680 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_436 v2)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'check_20868
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-fst-check
d_dt'45'fst'45'check_692 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'check_692 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'fst'45'check_692 v2 v3 v4 v5
du_dt'45'fst'45'check_692 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'check_692 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_448 v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'check_21464
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-snd-check
d_dt'45'snd'45'check_704 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'check_704 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'snd'45'check_704 v2 v3 v4 v5
du_dt'45'snd'45'check_704 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'check_704 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_460 v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'check_22060
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-terminal-morph-check
d_dt'45'terminal'45'morph'45'check_714 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'morph'45'check_714 ~v0 ~v1 v2 v3 v4
  = du_dt'45'terminal'45'morph'45'check_714 v2 v3 v4
du_dt'45'terminal'45'morph'45'check_714 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'morph'45'check_714 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_470
         v2)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'morph'45'check_22654
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-initial-morph-check
d_dt'45'initial'45'morph'45'check_724 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'morph'45'check_724 ~v0 ~v1 v2 v3 v4
  = du_dt'45'initial'45'morph'45'check_724 v2 v3 v4
du_dt'45'initial'45'morph'45'check_724 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'morph'45'check_724 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_480
         v2)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'morph'45'check_23248
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-inl-morph-check
d_dt'45'inl'45'morph'45'check_736 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'morph'45'check_736 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inl'45'morph'45'check_736 v2 v3 v4 v5
du_dt'45'inl'45'morph'45'check_736 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'morph'45'check_736 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_492
         v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'morph'45'check_23844
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-inr-morph-check
d_dt'45'inr'45'morph'45'check_748 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'morph'45'check_748 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inr'45'morph'45'check_748 v2 v3 v4 v5
du_dt'45'inr'45'morph'45'check_748 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'morph'45'check_748 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_504
         v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'morph'45'check_24440
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-compose-check-g
d_dt'45'compose'45'check'45'g_772 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'compose'45'check'45'g_772 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                  v9 ~v10 ~v11 v12 v13
  = du_dt'45'compose'45'check'45'g_772 v4 v5 v7 v8 v9 v12 v13
du_dt'45'compose'45'check'45'g_772 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'compose'45'check'45'g_772 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_524
         v1 v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'g_25048
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-compose-check-f
d_dt'45'compose'45'check'45'f_806 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'compose'45'check'45'f_806 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 ~v12 ~v13 v14 v15 v16
  = du_dt'45'compose'45'check'45'f_806
      v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16
du_dt'45'compose'45'check'45'f_806 ::
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
du_dt'45'compose'45'check'45'f_806 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_548
         v1 v3 v5 v6 v7 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         v9 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'f_25674
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe v9) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
-- Once.TypeCheck.DualWitness._.dt-case-copair-check
d_dt'45'case'45'copair'45'check_836 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'case'45'copair'45'check_836 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                    v9 ~v10 ~v11 v12 v13
  = du_dt'45'case'45'copair'45'check_836 v4 v5 v7 v8 v9 v12 v13
du_dt'45'case'45'copair'45'check_836 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'case'45'copair'45'check_836 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_568
         v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case'45'copair'45'check_26300
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-morph-check
d_dt'45'pair'45'morph'45'check_864 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair'45'morph'45'check_864 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
                                   v9 ~v10 ~v11 v12 v13
  = du_dt'45'pair'45'morph'45'check_864 v4 v7 v8 v9 v12 v13
du_dt'45'pair'45'morph'45'check_864 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'morph'45'check_864 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_588
         v2 v3 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'morph'45'check_26920
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-curry-check
d_dt'45'curry'45'check_890 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'curry'45'check_890 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 v10
                           v11
  = du_dt'45'curry'45'check_890 v3 v4 v6 v7 v10 v11
du_dt'45'curry'45'check_890 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'curry'45'check_890 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_608 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'curry'45'check_27538
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-cata-check
d_dt'45'cata'45'check_912 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'cata'45'check_912 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_dt'45'cata'45'check_912 v3 v5 v6 v8 v9 v10
du_dt'45'cata'45'check_912 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'cata'45'check_912 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_624 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'cata'45'check_28148
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-ana-check
d_dt'45'ana'45'check_940 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'ana'45'check_940 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 v9 v10 v11
                         v12
  = du_dt'45'ana'45'check_940 v3 v4 v5 v7 v9 v10 v11 v12
du_dt'45'ana'45'check_940 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'ana'45'check_940 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_644 v3 v4 v5
         v6 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'ana'45'check_28764
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
-- Once.TypeCheck.DualWitness._.dt-loop-check
d_dt'45'loop'45'check_960 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'loop'45'check_960 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_dt'45'loop'45'check_960 v3 v5 v7
du_dt'45'loop'45'check_960 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'loop'45'check_960 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_656 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'loop'45'check_29372
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-sub
d_dt'45'sub_976 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'sub_976 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_dt'45'sub_976 v3 v4 v7 v8
du_dt'45'sub_976 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'sub_976 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_668 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'sub_29978 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe v3))
-- Once.TypeCheck.DualWitness._.dt-lam
d_dt'45'lam_1004 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'lam_1004 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 v11 ~v12
                 v13
  = du_dt'45'lam_1004 v2 v4 v6 v7 v8 v11 v13
du_dt'45'lam_1004 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'lam_1004 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_690 v3 v5
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'lam_30596 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-lit-check
d_dt'45'pair'45'lit'45'check_1028 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'pair'45'lit'45'check_1028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8
                                  ~v9 v10 v11
  = du_dt'45'pair'45'lit'45'check_1028 v6 v7 v10 v11
du_dt'45'pair'45'lit'45'check_1028 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'lit'45'check_1028 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_706
         v0 v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'lit'45'check_31212
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-In-app-check
d_dt'45'In'45'app'45'check_1046 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'In'45'app'45'check_1046 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_dt'45'In'45'app'45'check_1046 v3 v4 v6 v7
du_dt'45'In'45'app'45'check_1046 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'In'45'app'45'check_1046 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_716 v1
         v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'In'45'app'45'check_31824
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-check
d_dt'45'apply'45'check_1062 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'check_1062 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'apply'45'check_1062 v3 v4 v5 v7
du_dt'45'apply'45'check_1062 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'check_1062 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_728 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'check_32434
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inl-app-check
d_dt'45'inl'45'app'45'check_1076 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'app'45'check_1076 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'inl'45'app'45'check_1076 v3 v4 v5 v7
du_dt'45'inl'45'app'45'check_1076 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'app'45'check_1076 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_740 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'app'45'check_33038
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inr-app-check
d_dt'45'inr'45'app'45'check_1090 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'app'45'check_1090 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'inr'45'app'45'check_1090 v3 v4 v5 v7
du_dt'45'inr'45'app'45'check_1090 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'app'45'check_1090 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_752 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'app'45'check_33642
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-initial-app-check
d_dt'45'initial'45'app'45'check_1102 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'app'45'check_1102 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'initial'45'app'45'check_1102 v3 v4 v6
du_dt'45'initial'45'app'45'check_1102 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'app'45'check_1102 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_762
         v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'app'45'check_34244
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate
d_dt'45'var'45'poly'45'instantiate_1118 ::
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
d_dt'45'var'45'poly'45'instantiate_1118 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
                                        ~v8 ~v9 ~v10 v11
  = du_dt'45'var'45'poly'45'instantiate_1118 v2 v4 v5 v6 v11
du_dt'45'var'45'poly'45'instantiate_1118 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate_1118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_776
         v1 v2 v3 v4)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate_34850
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.TypeCheck.DualWitness._.dd-infer
d_dd'45'infer_1150 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'infer_1150 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 v10 v11 v12
  = du_dd'45'infer_1150 v3 v4 v5 v6 v7 v10 v11 v12
du_dd'45'infer_1150 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'infer_1150 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_796 v1 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)) v6 v7)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'infer_35492
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)) (coe v6)
         (coe v7))
-- Once.TypeCheck.DualWitness._.dd-poly
d_dd'45'poly_1184 ::
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
d_dd'45'poly_1184 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                  ~v14 ~v15 v16 v17 v18 v19
  = du_dd'45'poly_1184
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v19
du_dd'45'poly_1184 ::
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
du_dd'45'poly_1184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_820 v4 v5 v6 v7 v8 v9
         v10 v11 v12 v13)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'poly_36116
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13))
-- Once.TypeCheck.DualWitness._.dd-lam
d_dd'45'lam_1220 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'lam_1220 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_dd'45'lam_1220 v2 v4 v6 v7 v10 v11
du_dd'45'lam_1220 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'lam_1220 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_840 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'lam_36758 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-compose
d_dd'45'compose_1246 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'compose_1246 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11
                     v12 v13
  = du_dd'45'compose_1246 v4 v5 v7 v8 v9 v12 v13
du_dd'45'compose_1246 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'compose_1246 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_860 v1 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'compose_37378
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dd-id
d_dd'45'id_1260 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'id_1260 ~v0 ~v1 v2 v3 v4 = du_dd'45'id_1260 v2 v3 v4
du_dd'45'id_1260 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'id_1260 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'id_870 v2)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'id_37984 (coe v0)
           (coe v1))
-- Once.TypeCheck.DualWitness._.dd-fst
d_dd'45'fst_1272 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'fst_1272 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'fst_1272 v2 v3 v4 v5
du_dd'45'fst_1272 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'fst_1272 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_882 v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'fst_38580 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-snd
d_dd'45'snd_1284 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'snd_1284 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'snd_1284 v2 v3 v4 v5
du_dd'45'snd_1284 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'snd_1284 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_894 v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'snd_39176 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-terminal
d_dd'45'terminal_1294 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'terminal_1294 ~v0 ~v1 v2 v3 v4
  = du_dd'45'terminal_1294 v2 v3 v4
du_dd'45'terminal_1294 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'terminal_1294 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_904 v2)
      (\ v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'terminal_39770
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dd-initial
d_dd'45'initial_1302 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'initial_1302 ~v0 ~v1 v2 v3 = du_dd'45'initial_1302 v2 v3
du_dd'45'initial_1302 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'initial_1302 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_912 v1)
      (\ v2 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'initial_40362
           (coe v0))
-- Once.TypeCheck.DualWitness._.dd-case
d_dd'45'case_1332 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'case_1332 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12
                  ~v13 v14 v15 v16
  = du_dd'45'case_1332 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16
du_dd'45'case_1332 ::
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
du_dd'45'case_1332 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'case_936 v2 v3 v6 v7
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)) v10)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'case_40976
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)) (coe v10))
-- Once.TypeCheck.DualWitness._.dd-pair
d_dd'45'pair_1362 ::
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
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'pair_1362 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
                  v13
  = du_dd'45'pair_1362 v4 v7 v8 v9 v12 v13
du_dd'45'pair_1362 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'pair_1362 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_956 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'pair_41608
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-cata
d_dd'45'cata_1386 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'cata_1386 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_dd'45'cata_1386 v3 v5 v6 v8 v9 v10
du_dd'45'cata_1386 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'cata_1386 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_972 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'cata_42224
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
