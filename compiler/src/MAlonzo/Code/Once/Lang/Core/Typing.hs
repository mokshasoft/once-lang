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

module MAlonzo.Code.Once.Lang.Core.Typing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.Typing._.Lit
d_Lit_18 a0 a1 a2 = ()
-- Once.Lang.Core.Typing._.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Lang.Core.Typing._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Lang.Core.Typing._.primCod
d_primCod_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primCod_102 ~v0 ~v1 ~v2 = du_primCod_102
du_primCod_102 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primCod_102
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primCod_58
-- Once.Lang.Core.Typing._.primDom
d_primDom_104 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primDom_104 ~v0 ~v1 ~v2 = du_primDom_104
du_primDom_104 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primDom_104
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56
-- Once.Lang.Core.Typing._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__248 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'8866''91'_'93'_'8759'_'33'__248
  = C_'8866'var_256 |
    C_'8866'lam_276 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'app_302 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__248
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'let_326 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__248
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'unit_332 |
    C_'8866'pair_354 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     T__'8866''91'_'93'_'8759'_'33'__248
                     T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'fst_370 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'snd_386 MAlonzo.Code.Once.Lang.Type.T_Type_8
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'inl_402 T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'inr_418 T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'case_448 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                     T__'8866''91'_'93'_'8759'_'33'__248
                     T__'8866''91'_'93'_'8759'_'33'__248
                     T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'absurd_462 T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'roll_476 MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                     T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'fold_500 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                     MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                     T__'8866''91'_'93'_'8759'_'33'__248
                     T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'unfold_524 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       MAlonzo.Code.Once.Lang.Context.T_Usage_46
                       MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                       MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                       MAlonzo.Code.Once.Lang.Type.T_Type_8
                       MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                       T__'8866''91'_'93'_'8759'_'33'__248
                       T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'out_540 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.T_Functor_6
                    MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
                    T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'coerce_556 MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
                       T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'lit'45'int_564 | C_'8866'lit'45'float_572 |
    C_'8866'prim_586 T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'sigop_598 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34
                      AgdaAny MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                      MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'ref_608 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) |
    C_'8866'sub'45'use_624 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                           MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
                           T__'8866''91'_'93'_'8759'_'33'__248 |
    C_'8866'sub'45'eff_640 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                           MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                           T__'8866''91'_'93'_'8759'_'33'__248
-- Once.Lang.Core.Typing.⊑ᵘ-keep
d_'8849''7512''45'keep_650 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_'8849''7512''45'keep_650 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_'8849''7512''45'keep_650 v4 v7
du_'8849''7512''45'keep_650 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_'8849''7512''45'keep_650 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe
             MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164) v1
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe
             MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170) v1
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe
             MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192
             (coe MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174) v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Typing.⊢case⊔
d_'8866'case'8852'_688 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'case'8852'_688 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                       v12 v13 ~v14 ~v15 ~v16 ~v17 v18 v19 v20
  = du_'8866'case'8852'_688
      v5 v6 v7 v8 v9 v10 v11 v12 v13 v18 v19 v20
du_'8866'case'8852'_688 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'case'8852'_688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      C_'8866'case_448 v0
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v1)
         (coe v2))
      v5 v6 v7 v8 v9
      (coe
         C_'8866'sub'45'use_624
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v3 v1)
         (coe
            du_'8849''7512''45'keep_650 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
               (coe v1) (coe v2)))
         v10)
      (coe
         C_'8866'sub'45'use_624
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v4 v2)
         (coe
            du_'8849''7512''45'keep_650 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
               (coe v1) (coe v2)))
         v11)
-- Once.Lang.Core.Typing.⊢let-pure
d_'8866'let'45'pure_724 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'let'45'pure_724 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10
                        ~v11 v12 v13 v14
  = du_'8866'let'45'pure_724 v5 v6 v7 v8 v12 v13 v14
du_'8866'let'45'pure_724 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'let'45'pure_724 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v4)
      (coe
         C_'8866'let_326 v0 v1
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v2 v3 v5 v6)
-- Once.Lang.Core.Typing.⊢app-pure
d_'8866'app'45'pure_758 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'app'45'pure_758 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10
                        ~v11 v12 v13 v14
  = du_'8866'app'45'pure_758 v5 v6 v7 v8 v12 v13 v14
du_'8866'app'45'pure_758 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248 ->
  T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'app'45'pure_758 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v4)
      (coe
         C_'8866'app_302 v0 v1 v4 v2
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v3 v5 v6)
