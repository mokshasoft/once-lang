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

module MAlonzo.Code.Once.Spec.Core.Typing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.Typing._.Lit
d_Lit_18 a0 a1 a2 = ()
-- Once.Spec.Core.Typing._.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Spec.Core.Typing._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Spec.Core.Typing._.primCod
d_primCod_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primCod_100 ~v0 ~v1 ~v2 = du_primCod_100
du_primCod_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primCod_100
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Spec.Core.Typing._.primDom
d_primDom_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primDom_102 ~v0 ~v1 ~v2 = du_primDom_102
du_primDom_102 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primDom_102
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Spec.Core.Typing._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'8866''91'_'93'_'8759'_'33'__244
  = C_'8866'var_252 |
    C_'8866'lam_272 MAlonzo.Code.Once.Type.T_Quantity_4
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'app_294 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Type_108
                    T__'8866''91'_'93'_'8759'_'33'__244
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'let_316 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Type.T_Type_108
                    T__'8866''91'_'93'_'8759'_'33'__244
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'unit_322 |
    C_'8866'pair_342 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'fst_358 MAlonzo.Code.Once.Type.T_Type_108
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'snd_374 MAlonzo.Code.Once.Type.T_Type_108
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'inl_390 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'inr_406 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'case_434 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.Type.T_Type_108
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'absurd_448 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'roll_462 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'fold_482 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Type.T_Functor_106
                     MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'unfold_504 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                       T__'8866''91'_'93'_'8759'_'33'__244
                       T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'out_518 MAlonzo.Code.Once.Type.T_Functor_106
                    MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'coerce_534 MAlonzo.Code.Once.Type.Sub.T__'60''58'__24
                       T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'lit'45'int_542 | C_'8866'lit'45'float_550 |
    C_'8866'prim_564 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'sigop_576 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222
                      AgdaAny MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                      MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'ref_586 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) |
    C_'8866'sub'45'use_602 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                           MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
                           T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'sub'45'eff_618 MAlonzo.Code.Once.Type.T_Purity_32
                           MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
                           T__'8866''91'_'93'_'8759'_'33'__244
-- Once.Spec.Core.Typing.⊑ᵘ-keep
d_'8849''7512''45'keep_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_'8849''7512''45'keep_628 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_'8849''7512''45'keep_628 v4 v7
du_'8849''7512''45'keep_628 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_'8849''7512''45'keep_628 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290
             (coe MAlonzo.Code.Once.Surface.Context.C_z'8804'z_262) v1
      MAlonzo.Code.Once.Type.C_One_8
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290
             (coe MAlonzo.Code.Once.Surface.Context.C_o'8804'o_268) v1
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290
             (coe MAlonzo.Code.Once.Surface.Context.C_m'8804'm_272) v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Typing.⊢case⊔
d_'8866'case'8852'_664 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'case'8852'_664 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 ~v10 v11
                       v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19
  = du_'8866'case'8852'_664 v5 v6 v7 v8 v9 v11 v12 v17 v18 v19
du_'8866'case'8852'_664 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'8852'_664 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      C_'8866'case_434 v0
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
      v3 v4 v5 v6 v7
      (coe
         C_'8866'sub'45'use_602
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v3 v1)
         (coe
            du_'8849''7512''45'keep_628 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
               (coe v1) (coe v2)))
         v8)
      (coe
         C_'8866'sub'45'use_602
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v4 v2)
         (coe
            du_'8849''7512''45'keep_628 (coe v4)
            (coe
               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
               (coe v1) (coe v2)))
         v9)
