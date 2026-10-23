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
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'int_2466 (coe v0))
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
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'float_3064
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
      (\ v0 v1 ->
         coe MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit_3660)
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
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'unit'45'var_4250)
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
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'local_4848
           (coe v0) (coe v1) (coe v2) (coe v3) v4)
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
      (\ v5 v6 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'resolved_5452
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) v5)
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
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'own_6074
           (coe v0) (coe v1) v2)
-- Once.TypeCheck.DualWitness._.dt-var-import
d_dt'45'var'45'import_182 ::
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
d_dt'45'var'45'import_182 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dt'45'var'45'import_182 v3 v8
du_dt'45'var'45'import_182 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'import_182 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'import_98 v0 v1)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'import_6684
           v3)
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate-infer
d_dt'45'var'45'poly'45'instantiate'45'infer_208 ::
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
d_dt'45'var'45'poly'45'instantiate'45'infer_208 ~v0 ~v1 v2 ~v3 v4
                                                v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_dt'45'var'45'poly'45'instantiate'45'infer_208
      v2 v4 v5 v6 v7 v11
du_dt'45'var'45'poly'45'instantiate'45'infer_208 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate'45'infer_208 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_114
         v1 v2 v3 v4 v5)
      (\ v6 v7 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate'45'infer_7292
           (coe v0) (coe v1) (coe v2) (coe v3) v6)
-- Once.TypeCheck.DualWitness._.dt-annot
d_dt'45'annot_232 ::
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
d_dt'45'annot_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_dt'45'annot_232 v7
du_dt'45'annot_232 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'annot_232 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_126
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'annot_7912
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-pair
d_dt'45'pair_254 ::
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
d_dt'45'pair_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_dt'45'pair_254 v6 v7 v10 v11
du_dt'45'pair_254 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair_254 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_142 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair_8544 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-neg
d_dt'45'neg_266 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg_266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_dt'45'neg_266 v5
du_dt'45'neg_266 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg_266 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_150
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg_9156
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.TypeCheck.DualWitness._.dt-neg-float
d_dt'45'neg'45'float_276 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'neg'45'float_276 ~v0 ~v1 v2 v3 v4
  = du_dt'45'neg'45'float_276 v2 v3 v4
du_dt'45'neg'45'float_276 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'neg'45'float_276 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_160)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'neg'45'float_9760
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-let
d_dt'45'let_304 ::
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
d_dt'45'let_304 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
                v13
  = du_dt'45'let_304 v2 v5 v7 v8 v9 v12 v13
du_dt'45'let_304 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'let_304 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'let_180 v1 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'let_10376 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-case
d_dt'45'case_348 ::
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
d_dt'45'case_348 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 ~v17 ~v18 ~v19 v20 v21 v22 v23
  = du_dt'45'case_348
      v3 v5 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v20 v21 v22 v23
du_dt'45'case_348 ::
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
du_dt'45'case_348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case_214 v2 v3 v4 v5 v7 v8
         v9 v10 v11 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v13))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v14)) v15)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case_11026
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v12))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v14)) (coe v15))
-- Once.TypeCheck.DualWitness._.dt-binop-arith
d_dt'45'binop'45'arith_374 ::
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
d_dt'45'binop'45'arith_374 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
                           v11
  = du_dt'45'binop'45'arith_374 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith_374 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith_374 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith_11676
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float
d_dt'45'binop'45'arith'45'float_398 ::
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
d_dt'45'binop'45'arith'45'float_398 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7
                                    ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float_398 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float_398 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float_398 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float_12302
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-il
d_dt'45'binop'45'arith'45'float'45'il_422 ::
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
d_dt'45'binop'45'arith'45'float'45'il_422 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float'45'il_422 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float'45'il_422 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'il_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'il_12928
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-arith-float-ir
d_dt'45'binop'45'arith'45'float'45'ir_446 ::
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
d_dt'45'binop'45'arith'45'float'45'ir_446 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
                                          ~v7 ~v8 ~v9 v10 v11
  = du_dt'45'binop'45'arith'45'float'45'ir_446 v2 v5 v6 v10 v11
du_dt'45'binop'45'arith'45'float'45'ir_446 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'arith'45'float'45'ir_446 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'arith'45'float'45'ir_13558
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-binop-cmp
d_dt'45'binop'45'cmp_470 ::
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
d_dt'45'binop'45'cmp_470 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
                         v11
  = du_dt'45'binop'45'cmp_470 v2 v5 v6 v10 v11
du_dt'45'binop'45'cmp_470 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'binop'45'cmp_470 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'binop'45'cmp_14188
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-app
d_dt'45'id'45'app_486 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'app_486 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'id'45'app_486 v3 v4 v6
du_dt'45'id'45'app_486 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'app_486 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_294 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'app_14806
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-fst-app
d_dt'45'fst'45'app_500 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'app_500 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'fst'45'app_500 v3 v4 v5 v7
du_dt'45'fst'45'app_500 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'app_500 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_306 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'app_15414
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-snd-app
d_dt'45'snd'45'app_514 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'app_514 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'snd'45'app_514 v3 v4 v5 v7
du_dt'45'snd'45'app_514 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'app_514 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_318 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'app_16022
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-terminal-app
d_dt'45'terminal'45'app_526 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'app_526 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'terminal'45'app_526 v3 v4 v6
du_dt'45'terminal'45'app_526 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'app_526 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_328 v0 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'app_16628
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-apply-app-infer
d_dt'45'apply'45'app'45'infer_540 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'app'45'infer_540 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'apply'45'app'45'infer_540 v3 v4 v5 v7
du_dt'45'apply'45'app'45'infer_540 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'app'45'infer_540 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_340
         v0 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'app'45'infer_17236
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-eff-app-infer
d_dt'45'apply'45'eff'45'app'45'infer_558 ::
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
d_dt'45'apply'45'eff'45'app'45'infer_558 ~v0 ~v1 ~v2 v3 v4 v5 v6
                                         ~v7 v8 v9
  = du_dt'45'apply'45'eff'45'app'45'infer_558 v3 v4 v5 v6 v8 v9
du_dt'45'apply'45'eff'45'app'45'infer_558 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'eff'45'app'45'infer_558 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_356
         v0 v2 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'eff'45'app'45'infer_17848
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-Out-app-infer
d_dt'45'Out'45'app'45'infer_580 ::
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
d_dt'45'Out'45'app'45'infer_580 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9
  = du_dt'45'Out'45'app'45'infer_580 v3 v5 v7 v9
du_dt'45'Out'45'app'45'infer_580 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'app'45'infer_580 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_368 v0
         v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'app'45'infer_18464
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-Out-eff-app-infer
d_dt'45'Out'45'eff'45'app'45'infer_606 ::
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
d_dt'45'Out'45'eff'45'app'45'infer_606 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
                                       ~v8 v9
  = du_dt'45'Out'45'eff'45'app'45'infer_606 v3 v5 v7 v9
du_dt'45'Out'45'eff'45'app'45'infer_606 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'Out'45'eff'45'app'45'infer_606 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_380
         v0 v1 v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'Out'45'eff'45'app'45'infer_19086
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-app
d_dt'45'app_632 ::
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
d_dt'45'app_632 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 v12
                v13
  = du_dt'45'app_632 v4 v6 v7 v8 v12 v13
du_dt'45'app_632 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app_632 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app_398 v0 v1 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app_19708 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-effApp
d_dt'45'effApp_660 ::
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
d_dt'45'effApp_660 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 v11
                   ~v12 v13 v14
  = du_dt'45'effApp_660 v4 v6 v7 v8 v11 v13 v14
du_dt'45'effApp_660 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'effApp_660 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_418 v0 v1 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'effApp_20336
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-app-spine
d_dt'45'app'45'spine_686 ::
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
d_dt'45'app'45'spine_686 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                         v11 v12
  = du_dt'45'app'45'spine_686 v4 v6 v7 v11 v12
du_dt'45'app'45'spine_686 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'app'45'spine_686 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_434 v0 v1 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'app'45'spine_20962
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
-- Once.TypeCheck.DualWitness._.dt-id-check
d_dt'45'id'45'check_700 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'id'45'check_700 ~v0 ~v1 v2 v3 v4
  = du_dt'45'id'45'check_700 v2 v3 v4
du_dt'45'id'45'check_700 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'id'45'check_700 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_446 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'id'45'check_21600
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-fst-check
d_dt'45'fst'45'check_712 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'fst'45'check_712 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'fst'45'check_712 v2 v3 v4 v5
du_dt'45'fst'45'check_712 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'fst'45'check_712 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_458 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'fst'45'check_22198
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-snd-check
d_dt'45'snd'45'check_724 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'snd'45'check_724 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'snd'45'check_724 v2 v3 v4 v5
du_dt'45'snd'45'check_724 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'snd'45'check_724 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_470 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'snd'45'check_22796
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-terminal-morph-check
d_dt'45'terminal'45'morph'45'check_734 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'terminal'45'morph'45'check_734 ~v0 ~v1 v2 v3 v4
  = du_dt'45'terminal'45'morph'45'check_734 v2 v3 v4
du_dt'45'terminal'45'morph'45'check_734 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'terminal'45'morph'45'check_734 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_480
         v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'terminal'45'morph'45'check_23392
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-initial-morph-check
d_dt'45'initial'45'morph'45'check_744 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'morph'45'check_744 ~v0 ~v1 v2 v3 v4
  = du_dt'45'initial'45'morph'45'check_744 v2 v3 v4
du_dt'45'initial'45'morph'45'check_744 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'morph'45'check_744 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_490
         v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'morph'45'check_23988
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dt-inl-morph-check
d_dt'45'inl'45'morph'45'check_756 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'morph'45'check_756 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inl'45'morph'45'check_756 v2 v3 v4 v5
du_dt'45'inl'45'morph'45'check_756 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'morph'45'check_756 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_502
         v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'morph'45'check_24586
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-inr-morph-check
d_dt'45'inr'45'morph'45'check_768 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'morph'45'check_768 ~v0 ~v1 v2 v3 v4 v5
  = du_dt'45'inr'45'morph'45'check_768 v2 v3 v4 v5
du_dt'45'inr'45'morph'45'check_768 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'morph'45'check_768 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_514
         v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'morph'45'check_25184
           (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dt-compose-check-g
d_dt'45'compose'45'check'45'g_792 ::
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
d_dt'45'compose'45'check'45'g_792 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                  v9 ~v10 ~v11 v12 v13
  = du_dt'45'compose'45'check'45'g_792 v4 v5 v7 v8 v9 v12 v13
du_dt'45'compose'45'check'45'g_792 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'compose'45'check'45'g_792 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_534
         v1 v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'g_25794
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-compose-check-f
d_dt'45'compose'45'check'45'f_826 ::
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
d_dt'45'compose'45'check'45'f_826 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 ~v12 ~v13 v14 v15 v16
  = du_dt'45'compose'45'check'45'f_826
      v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16
du_dt'45'compose'45'check'45'f_826 ::
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
du_dt'45'compose'45'check'45'f_826 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_558
         v1 v3 v5 v6 v7 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         v9 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'compose'45'check'45'f_26426
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe v9) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
-- Once.TypeCheck.DualWitness._.dt-case-copair-check
d_dt'45'case'45'copair'45'check_856 ::
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
d_dt'45'case'45'copair'45'check_856 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
                                    v9 ~v10 ~v11 v12 v13
  = du_dt'45'case'45'copair'45'check_856 v4 v5 v7 v8 v9 v12 v13
du_dt'45'case'45'copair'45'check_856 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'case'45'copair'45'check_856 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_578
         v3 v4 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'case'45'copair'45'check_27058
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-morph-check
d_dt'45'pair'45'morph'45'check_884 ::
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
d_dt'45'pair'45'morph'45'check_884 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
                                   v9 ~v10 ~v11 v12 v13
  = du_dt'45'pair'45'morph'45'check_884 v4 v7 v8 v9 v12 v13
du_dt'45'pair'45'morph'45'check_884 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'morph'45'check_884 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_598
         v2 v3 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'morph'45'check_27684
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-curry-check
d_dt'45'curry'45'check_910 ::
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
d_dt'45'curry'45'check_910 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 v10
                           v11
  = du_dt'45'curry'45'check_910 v3 v4 v6 v7 v10 v11
du_dt'45'curry'45'check_910 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'curry'45'check_910 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_618 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'curry'45'check_28308
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-cata-check
d_dt'45'cata'45'check_932 ::
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
d_dt'45'cata'45'check_932 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_dt'45'cata'45'check_932 v3 v5 v6 v8 v9 v10
du_dt'45'cata'45'check_932 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'cata'45'check_932 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_634 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'cata'45'check_28922
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dt-ana-check
d_dt'45'ana'45'check_960 ::
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
d_dt'45'ana'45'check_960 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 v9 v10 v11
                         v12
  = du_dt'45'ana'45'check_960 v3 v4 v5 v7 v9 v10 v11 v12
du_dt'45'ana'45'check_960 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'ana'45'check_960 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_654 v3 v4 v5
         v6 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'ana'45'check_29542
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
-- Once.TypeCheck.DualWitness._.dt-loop-check
d_dt'45'loop'45'check_980 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'loop'45'check_980 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_dt'45'loop'45'check_980 v3 v5 v7
du_dt'45'loop'45'check_980 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'loop'45'check_980 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_666 v1
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'loop'45'check_30154
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-sub
d_dt'45'sub_996 ::
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
d_dt'45'sub_996 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_dt'45'sub_996 v3 v4 v7 v8
du_dt'45'sub_996 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'sub_996 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'sub_30764 (coe v0)
         (coe v1) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe v3))
-- Once.TypeCheck.DualWitness._.dt-lam
d_dt'45'lam_1024 ::
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
d_dt'45'lam_1024 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 v11 ~v12
                 v13
  = du_dt'45'lam_1024 v2 v4 v6 v7 v8 v11 v13
du_dt'45'lam_1024 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'lam_1024 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_700 v3 v5
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'lam_31386 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dt-pair-lit-check
d_dt'45'pair'45'lit'45'check_1048 ::
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
d_dt'45'pair'45'lit'45'check_1048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8
                                  ~v9 v10 v11
  = du_dt'45'pair'45'lit'45'check_1048 v6 v7 v10 v11
du_dt'45'pair'45'lit'45'check_1048 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'pair'45'lit'45'check_1048 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_716
         v0 v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'pair'45'lit'45'check_32006
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-In-app-check
d_dt'45'In'45'app'45'check_1066 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'In'45'app'45'check_1066 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_dt'45'In'45'app'45'check_1066 v3 v4 v6 v7
du_dt'45'In'45'app'45'check_1066 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'In'45'app'45'check_1066 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_726 v1
         v2 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'In'45'app'45'check_32624
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-apply-check
d_dt'45'apply'45'check_1082 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'apply'45'check_1082 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'apply'45'check_1082 v3 v4 v5 v7
du_dt'45'apply'45'check_1082 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'apply'45'check_1082 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_738 v0 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'apply'45'check_33238
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inl-app-check
d_dt'45'inl'45'app'45'check_1096 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inl'45'app'45'check_1096 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'inl'45'app'45'check_1096 v3 v4 v5 v7
du_dt'45'inl'45'app'45'check_1096 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inl'45'app'45'check_1096 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_750 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inl'45'app'45'check_33846
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-inr-app-check
d_dt'45'inr'45'app'45'check_1110 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'inr'45'app'45'check_1110 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_dt'45'inr'45'app'45'check_1110 v3 v4 v5 v7
du_dt'45'inr'45'app'45'check_1110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'inr'45'app'45'check_1110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_762 v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'inr'45'app'45'check_34454
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
-- Once.TypeCheck.DualWitness._.dt-initial-app-check
d_dt'45'initial'45'app'45'check_1122 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dt'45'initial'45'app'45'check_1122 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_dt'45'initial'45'app'45'check_1122 v3 v4 v6
du_dt'45'initial'45'app'45'check_1122 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'initial'45'app'45'check_1122 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_772
         v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'initial'45'app'45'check_35060
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Once.TypeCheck.DualWitness._.dt-var-poly-instantiate
d_dt'45'var'45'poly'45'instantiate_1138 ::
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
d_dt'45'var'45'poly'45'instantiate_1138 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
                                        ~v8 ~v9 ~v10 v11
  = du_dt'45'var'45'poly'45'instantiate_1138 v2 v4 v5 v6 v11
du_dt'45'var'45'poly'45'instantiate_1138 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dt'45'var'45'poly'45'instantiate_1138 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_786
         v1 v2 v3 v4)
      (\ v5 v6 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wt'45'var'45'poly'45'instantiate_35670
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) v5)
-- Once.TypeCheck.DualWitness._.dd-infer
d_dd'45'infer_1170 ::
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
d_dd'45'infer_1170 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 v10 v11 v12
  = du_dd'45'infer_1170 v3 v4 v5 v6 v7 v10 v11 v12
du_dd'45'infer_1170 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'infer_1170 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_806 v1 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)) v6 v7)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'infer_36314
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)) (coe v6)
         (coe v7))
-- Once.TypeCheck.DualWitness._.dd-poly
d_dd'45'poly_1204 ::
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
d_dd'45'poly_1204 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                  ~v14 ~v15 v16 v17 v18 v19
  = du_dd'45'poly_1204
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v19
du_dd'45'poly_1204 ::
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
du_dd'45'poly_1204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_830 v4 v5 v6 v7 v8 v9
         v10 v11 v12 v13)
      (\ v14 v15 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'poly_36942
           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
           (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
           v14)
-- Once.TypeCheck.DualWitness._.dd-lam
d_dd'45'lam_1240 ::
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
d_dd'45'lam_1240 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_dd'45'lam_1240 v2 v4 v6 v7 v10 v11
du_dd'45'lam_1240 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'lam_1240 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_850 v2 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'lam_37586 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-compose
d_dd'45'compose_1266 ::
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
d_dd'45'compose_1266 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11
                     v12 v13
  = du_dd'45'compose_1266 v4 v5 v7 v8 v9 v12 v13
du_dd'45'compose_1266 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'compose_1266 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_870 v1 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'compose_38210
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Once.TypeCheck.DualWitness._.dd-id
d_dd'45'id_1280 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'id_1280 ~v0 ~v1 v2 v3 v4 = du_dd'45'id_1280 v2 v3 v4
du_dd'45'id_1280 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'id_1280 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'id_880 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'id_38822 (coe v0)
           (coe v1))
-- Once.TypeCheck.DualWitness._.dd-fst
d_dd'45'fst_1292 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'fst_1292 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'fst_1292 v2 v3 v4 v5
du_dd'45'fst_1292 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'fst_1292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_892 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'fst_39420 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-snd
d_dd'45'snd_1304 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'snd_1304 ~v0 ~v1 v2 v3 v4 v5
  = du_dd'45'snd_1304 v2 v3 v4 v5
du_dd'45'snd_1304 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'snd_1304 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_904 v3)
      (\ v4 v5 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'snd_40018 (coe v0)
           (coe v1) (coe v2))
-- Once.TypeCheck.DualWitness._.dd-terminal
d_dd'45'terminal_1314 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'terminal_1314 ~v0 ~v1 v2 v3 v4
  = du_dd'45'terminal_1314 v2 v3 v4
du_dd'45'terminal_1314 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'terminal_1314 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_914 v2)
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'terminal_40614
           (coe v0) (coe v1))
-- Once.TypeCheck.DualWitness._.dd-initial
d_dd'45'initial_1322 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dd'45'initial_1322 ~v0 ~v1 v2 v3 = du_dd'45'initial_1322 v2 v3
du_dd'45'initial_1322 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'initial_1322 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_922 v1)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'initial_41208
           (coe v0))
-- Once.TypeCheck.DualWitness._.dd-case
d_dd'45'case_1352 ::
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
d_dd'45'case_1352 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12
                  ~v13 v14 v15 v16
  = du_dd'45'case_1352 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16
du_dd'45'case_1352 ::
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
du_dd'45'case_1352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'case_946 v2 v3 v6 v7
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)) v10)
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'case_41824
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)) (coe v10))
-- Once.TypeCheck.DualWitness._.dd-pair
d_dd'45'pair_1382 ::
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
d_dd'45'pair_1382 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
                  v13
  = du_dd'45'pair_1382 v4 v7 v8 v9 v12 v13
du_dd'45'pair_1382 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'pair_1382 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_966 v2 v3
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'pair_42462
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Once.TypeCheck.DualWitness._.dd-cata
d_dd'45'cata_1406 ::
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
d_dd'45'cata_1406 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_dd'45'cata_1406 v3 v5 v6 v8 v9 v10
du_dd'45'cata_1406 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dd'45'cata_1406 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_982 v2 v3 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         MAlonzo.Code.Once.TypeCheck.SpecWitness.du_wd'45'cata_43084
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
