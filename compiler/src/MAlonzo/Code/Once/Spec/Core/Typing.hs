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
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed

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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_primCod_100 ~v0 ~v1 ~v2 = du_primCod_100
du_primCod_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_primCod_100
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Spec.Core.Typing._.primDom
d_primDom_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_primDom_102 ~v0 ~v1 ~v2 = du_primDom_102
du_primDom_102 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_primDom_102
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Spec.Core.Typing._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'8866''91'_'93'_'8759'_'33'__244
  = C_'8866'var_252 |
    C_'8866'lam_272 MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'app_294 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                    MAlonzo.Code.Once.Spec.Context.T_Usage_46
                    MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Spec.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__244
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'let_316 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                    MAlonzo.Code.Once.Spec.Context.T_Usage_46
                    MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Spec.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__244
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'unit_322 |
    C_'8866'pair_342 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'fst_358 MAlonzo.Code.Once.Spec.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'snd_374 MAlonzo.Code.Once.Spec.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'inl_390 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'inr_406 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'case_434 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
                     MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
                     MAlonzo.Code.Once.Spec.Type.T_Type_8
                     MAlonzo.Code.Once.Spec.Type.T_Type_8
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'absurd_448 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'roll_462 MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'fold_482 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     MAlonzo.Code.Once.Spec.Context.T_Usage_46
                     MAlonzo.Code.Once.Spec.Type.T_Functor_6
                     MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
                     T__'8866''91'_'93'_'8759'_'33'__244
                     T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'unfold_504 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                       MAlonzo.Code.Once.Spec.Context.T_Usage_46
                       MAlonzo.Code.Once.Spec.Type.T_Type_8
                       MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
                       T__'8866''91'_'93'_'8759'_'33'__244
                       T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'out_518 MAlonzo.Code.Once.Spec.Type.T_Functor_6
                    MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
                    T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'coerce_534 MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20
                       T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'lit'45'int_542 | C_'8866'lit'45'float_550 |
    C_'8866'prim_564 T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'sigop_576 MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34
                      AgdaAny MAlonzo.Code.Once.Spec.Type.WellFormed.T_RigidFree_68
                      MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'ref_586 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) |
    C_'8866'sub'45'use_602 MAlonzo.Code.Once.Spec.Context.T_Usage_46
                           MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178
                           T__'8866''91'_'93'_'8759'_'33'__244 |
    C_'8866'sub'45'eff_618 MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28
                           MAlonzo.Code.Once.Spec.Type.Sub.T__'8849'π__8
                           T__'8866''91'_'93'_'8759'_'33'__244
-- Once.Spec.Core.Typing.⊑ᵘ-keep
d_'8849''7512''45'keep_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178
d_'8849''7512''45'keep_628 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_'8849''7512''45'keep_628 v4 v7
du_'8849''7512''45'keep_628 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178
du_'8849''7512''45'keep_628 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Spec.Context.C_z'8804'z_164) v1
      MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Spec.Context.C_o'8804'o_170) v1
      MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
        -> coe
             MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Spec.Context.C_m'8804'm_174) v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Typing.⊢case⊔
d_'8866'case'8852'_664 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
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
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244 ->
  T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'8852'_664 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      C_'8866'case_434 v0
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v1)
         (coe v2))
      v3 v4 v5 v6 v7
      (coe
         C_'8866'sub'45'use_602
         (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__52 v3 v1)
         (coe
            du_'8849''7512''45'keep_628 (coe v3)
            (coe
               MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''8852''737'_330
               (coe v1) (coe v2)))
         v8)
      (coe
         C_'8866'sub'45'use_602
         (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__52 v4 v2)
         (coe
            du_'8849''7512''45'keep_628 (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''8852''691'_346
               (coe v1) (coe v2)))
         v9)
