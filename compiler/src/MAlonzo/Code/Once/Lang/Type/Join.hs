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

module MAlonzo.Code.Once.Lang.Type.Join where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Lang.Type.Join.⊔p-ˡ
d_'8852'p'45''737'_12 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45''737'_12 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.⊔p-ʳ
d_'8852'p'45''691'_18 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45''691'_18 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.⊔p-least
d_'8852'p'45'least_28 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45'least_28 ~v0 ~v1 ~v2 v3 v4
  = du_'8852'p'45'least_28 v3 v4
du_'8852'p'45'least_28 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
du_'8852'p'45'least_28 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v0
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join._⊔f_
d__'8852'f__36 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40
d__'8852'f__36 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.⊔f-ˡ
d_'8852'f'45''737'_44 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'f'45''737'_44 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.⊔f-ʳ
d_'8852'f'45''691'_50 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'f'45''691'_50 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> coe
             MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
             (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v1))
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.⊔f-least
d_'8852'f'45'least_60 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'f'45'least_60 v0 ~v1 ~v2 v3 v4
  = du_'8852'f'45'least_60 v0 v3 v4
du_'8852'f'45'least_60 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
du_'8852'f'45'least_60 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42 -> coe v2
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.shape
d_shape_66 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Integer
d_shape_66 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2 -> coe (3 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe (4 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1 -> coe (5 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe (6 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe (7 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe (8 :: Integer)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2 -> coe (9 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.<:ᶜ-shape
d_'60''58''7580''45'shape_72 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''7580''45'shape_72 = erased
-- Once.Lang.Type.Join.UB
d_UB_76 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_UB_76 = erased
-- Once.Lang.Type.Join.Joins
d_Joins_84 a0 a1 a2 = ()
data T_Joins_84
  = C_j'45'refl_88 | C_j'45'void'737'_92 | C_j'45'void'691'_96 |
    C_j'45'prod_110 T_Joins_84 T_Joins_84 |
    C_j'45'sum_124 T_Joins_84 T_Joins_84 | C_j'45'arr_140 T_Joins_84 |
    C_j'45'ν_148
-- Once.Lang.Type.Join.Join?
d_Join'63'_154 a0 a1 = ()
data T_Join'63'_154
  = C_joined_162 MAlonzo.Code.Once.Lang.Type.T_Type_8 T_Joins_84 |
    C_apart_164
-- Once.Lang.Type.Join.reflJ
d_reflJ_168 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240
d_reflJ_168 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
      (coe
         MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''45'refl_210
         (coe v0))
      (coe
         MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''45'refl_210
         (coe v0))
      (coe (\ v1 v2 v3 -> v2))
-- Once.Lang.Type.Join.voidˡ
d_void'737'_178 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240
d_void'737'_178 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'void_126)
      (coe
         MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''45'refl_210
         (coe v0))
      (coe (\ v1 v2 v3 -> v3))
-- Once.Lang.Type.Join.voidʳ
d_void'691'_188 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240
d_void'691'_188 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
      (coe
         MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''45'refl_210
         (coe v0))
      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'void_126)
      (coe (\ v1 v2 v3 -> v2))
-- Once.Lang.Type.Join.clashJ
d_clashJ_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
d_clashJ_200 v0 v1 ~v2 v3 v4 = du_clashJ_200 v0 v1 v3 v4
du_clashJ_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
du_clashJ_200 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5) (coe C_joined_162 (coe v1) (coe C_j'45'void'737'_92))
             else coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe C_joined_162 (coe v0) (coe C_j'45'void'691'_96))
                              else coe seq (coe v7) (coe C_apart_164)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.prod-least
d_prod'45'least_232 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
d_prod'45'least_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_prod'45'least_232 v6 v7 v8 v9 v10
du_prod'45'least_232 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
du_prod'45'least_232 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156
                           (coe MAlonzo.Code.Once.Lang.Type.Sub.d_least_262 v1 v11 v9 v17)
                           (coe MAlonzo.Code.Once.Lang.Type.Sub.d_least_262 v2 v12 v10 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.prod-fst
d_prod'45'fst_254 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prod'45'fst_254 ~v0 ~v1 ~v2 ~v3 v4 = du_prod'45'fst_254 v4
du_prod'45'fst_254 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prod'45'fst_254 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v17 v18
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                            (coe v17))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.prod-snd
d_prod'45'snd_268 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prod'45'snd_268 ~v0 ~v1 ~v2 ~v3 v4 = du_prod'45'snd_268 v4
du_prod'45'snd_268 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prod'45'snd_268 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v17 v18
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                            (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.prodJ
d_prodJ_282 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Join'63'_154 -> T_Join'63'_154 -> T_Join'63'_154
d_prodJ_282 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_prodJ_282 v4 v5
du_prodJ_282 :: T_Join'63'_154 -> T_Join'63'_154 -> T_Join'63'_154
du_prodJ_282 v0 v1
  = case coe v0 of
      C_joined_162 v2 v3
        -> case coe v1 of
             C_joined_162 v4 v5
               -> coe
                    C_joined_162
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v4))
                    (coe C_j'45'prod_110 v3 v5)
             C_apart_164 -> coe C_apart_164
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apart_164 -> coe C_apart_164
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.sum-least
d_sum'45'least_314 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
d_sum'45'least_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_sum'45'least_314 v6 v7 v8 v9 v10
du_sum'45'least_314 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
du_sum'45'least_314 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166
                           (coe MAlonzo.Code.Once.Lang.Type.Sub.d_least_262 v1 v11 v9 v17)
                           (coe MAlonzo.Code.Once.Lang.Type.Sub.d_least_262 v2 v12 v10 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.sum-inl
d_sum'45'inl_336 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sum'45'inl_336 ~v0 ~v1 ~v2 ~v3 v4 = du_sum'45'inl_336 v4
du_sum'45'inl_336 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sum'45'inl_336 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v17 v18
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                            (coe v17))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.sum-inr
d_sum'45'inr_350 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sum'45'inr_350 ~v0 ~v1 ~v2 ~v3 v4 = du_sum'45'inr_350 v4
du_sum'45'inr_350 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sum'45'inr_350 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v17 v18
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                            (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.sumJ
d_sumJ_364 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Join'63'_154 -> T_Join'63'_154 -> T_Join'63'_154
d_sumJ_364 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sumJ_364 v4 v5
du_sumJ_364 :: T_Join'63'_154 -> T_Join'63'_154 -> T_Join'63'_154
du_sumJ_364 v0 v1
  = case coe v0 of
      C_joined_162 v2 v3
        -> case coe v1 of
             C_joined_162 v4 v5
               -> coe
                    C_joined_162
                    (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v2) (coe v4))
                    (coe C_j'45'sum_124 v3 v5)
             C_apart_164 -> coe C_apart_164
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apart_164 -> coe C_apart_164
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.arr-least
d_arr'45'least_398 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
d_arr'45'least_398 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_arr'45'least_398 v4 v8 v9 v10
du_arr'45'least_398 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
du_arr'45'least_398 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146
                           (coe MAlonzo.Code.Once.Lang.Type.Sub.d_least_262 v1 v14 v10 v21)
                           (coe du_'8852'p'45'least_28 (coe v11) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.arr-cod
d_arr'45'cod_422 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arr'45'cod_422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_arr'45'cod_422 v6
du_arr'45'cod_422 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arr'45'cod_422 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146 v11 v12
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146 v22 v23
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                            (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.arr-dom
d_arr'45'dom_440 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45'dom_440 = erased
-- Once.Lang.Type.Join.arr-q
d_arr'45'q_458 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45'q_458 = erased
-- Once.Lang.Type.Join.arrJ
d_arrJ_476 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154 -> T_Join'63'_154
d_arrJ_476 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10
  = du_arrJ_476 v0 v4 v6 v7 v8 v9 v10
du_arrJ_476 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154 -> T_Join'63'_154
du_arrJ_476 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (case coe v6 of
                                        C_joined_162 v11 v12
                                          -> coe
                                               C_joined_162
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                  (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.d__'8852'p__48
                                                        (coe v2) (coe v3)))
                                                  (coe v11))
                                               (coe C_j'45'arr_140 v12)
                                        C_apart_164 -> coe C_apart_164
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe seq (coe v10) (coe C_apart_164)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v8) (coe C_apart_164)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.eqJ
d_eqJ_506 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  ((MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Join'63'_154
d_eqJ_506 v0 ~v1 v2 ~v3 = du_eqJ_506 v0 v2
du_eqJ_506 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
du_eqJ_506 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe C_joined_162 (coe v0) (coe C_j'45'refl_88))
             else coe seq (coe v3) (coe C_apart_164)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.μ-apart
d_μ'45'apart_518 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_μ'45'apart_518 = erased
-- Once.Lang.Type.Join.rigid-apart
d_rigid'45'apart_530 ::
  MAlonzo.Code.Once.Lang.Type.T_TKind_10 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_TKind_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rigid'45'apart_530 = erased
-- Once.Lang.Type.Join.ν-least
d_ν'45'least_542 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
d_ν'45'least_542 ~v0 v1 ~v2 ~v3 v4 v5 = du_ν'45'least_542 v1 v4 v5
du_ν'45'least_542 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122
du_ν'45'least_542 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178 v10
               -> coe
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178
                    (coe du_'8852'f'45'least_60 (coe v0) (coe v6) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.ν-apart
d_ν'45'apart_556 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ν'45'apart_556 = erased
-- Once.Lang.Type.Join.νJ
d_νJ_568 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
d_νJ_568 v0 ~v1 v2 v3 v4 = du_νJ_568 v0 v2 v3 v4
du_νJ_568 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
du_νJ_568 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       C_joined_162
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v0)
                          (coe d__'8852'f__36 (coe v1) (coe v2)))
                       (coe C_j'45'ν_148))
             else coe seq (coe v5) (coe C_apart_164)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.join?
d_join'63'_582 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T_Join'63'_154
d_join'63'_582 v0 v1
  = coe
      d_joinS_588 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe d_shape_66 (coe v0)) (coe d_shape_66 (coe v1)))
-- Once.Lang.Type.Join.joinS
d_joinS_588 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_154
d_joinS_588 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v0 of
                    MAlonzo.Code.Once.Lang.Type.C_Unit_20
                      -> coe
                           seq (coe v4)
                           (coe seq (coe v1) (coe C_joined_162 (coe v0) (coe C_j'45'refl_88)))
                    MAlonzo.Code.Once.Lang.Type.C_Void_22
                      -> coe
                           seq (coe v4)
                           (coe seq (coe v1) (coe C_joined_162 (coe v0) (coe C_j'45'refl_88)))
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v5 v6
                      -> coe
                           seq (coe v4)
                           (case coe v1 of
                              MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
                                -> coe
                                     du_prodJ_282 (coe d_join'63'_582 (coe v5) (coe v7))
                                     (coe d_join'63'_582 (coe v6) (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v5 v6
                      -> coe
                           seq (coe v4)
                           (case coe v1 of
                              MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
                                -> coe
                                     du_sumJ_364 (coe d_join'63'_582 (coe v5) (coe v7))
                                     (coe d_join'63'_582 (coe v6) (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v5 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v8 v9
                             -> coe
                                  seq (coe v4)
                                  (case coe v1 of
                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v10 v11 v12
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v13 v14
                                              -> coe
                                                   du_arrJ_476 (coe v5) (coe v8) (coe v9) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
                                                      (coe v5) (coe v10))
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'q__8
                                                      (coe v8) (coe v13))
                                                   (coe d_join'63'_582 (coe v7) (coe v12))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v5
                      -> coe
                           seq (coe v4)
                           (coe
                              seq (coe v1)
                              (coe
                                 du_eqJ_506 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v0)
                                    (coe v1))))
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v5 v6
                      -> coe
                           seq (coe v4)
                           (case coe v1 of
                              MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v7 v8
                                -> coe
                                     du_νJ_568 (coe v5) (coe v6) (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'F__214 (coe v5)
                                        (coe v7))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Lang.Type.C_Int_34
                      -> coe
                           seq (coe v4)
                           (coe seq (coe v1) (coe C_joined_162 (coe v0) (coe C_j'45'refl_88)))
                    MAlonzo.Code.Once.Lang.Type.C_Float_36
                      -> coe
                           seq (coe v4)
                           (coe seq (coe v1) (coe C_joined_162 (coe v0) (coe C_j'45'refl_88)))
                    MAlonzo.Code.Once.Lang.Type.C_rigid_38 v5 v6
                      -> coe
                           seq (coe v4)
                           (coe
                              seq (coe v1)
                              (coe
                                 du_eqJ_506 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v0)
                                    (coe v1))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4)
                    (coe
                       du_clashJ_200 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v0)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Void_22))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v1)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.sound
d_sound_658 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Joins_84 -> MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240
d_sound_658 v0 v1 v2 v3
  = case coe v3 of
      C_j'45'refl_88 -> coe d_reflJ_168 (coe v0)
      C_j'45'void'737'_92 -> coe d_void'737'_178 (coe v1)
      C_j'45'void'691'_96 -> coe d_void'691'_188 (coe v0)
      C_j'45'prod_110 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                        (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                        (coe d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                        (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                        (coe d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          du_prod'45'least_232 (coe v18)
                                          (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10))
                                          (coe
                                             d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'sum_124 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                        (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                        (coe d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                        (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                        (coe d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          du_sum'45'least_314 (coe v18)
                                          (coe d_sound_658 (coe v12) (coe v14) (coe v16) (coe v10))
                                          (coe
                                             d_sound_658 (coe v13) (coe v15) (coe v17) (coe v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'arr_140 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v15 v16
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v20 v21
                                    -> case coe v2 of
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v22 v23 v24
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146
                                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                                      (coe
                                                         d_sound_658 (coe v14) (coe v19) (coe v24)
                                                         (coe v11)))
                                                   (d_'8852'p'45''737'_12 (coe v16) (coe v21)))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146
                                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                                      (coe
                                                         d_sound_658 (coe v14) (coe v19) (coe v24)
                                                         (coe v11)))
                                                   (d_'8852'p'45''691'_18 (coe v16) (coe v21)))
                                                (coe
                                                   (\ v25 ->
                                                      coe
                                                        du_arr'45'least_398 (coe v25)
                                                        (coe
                                                           d_sound_658 (coe v14) (coe v19) (coe v24)
                                                           (coe v11))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'ν_148
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Lang.Type.Sub.C_constructor_264
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178
                              (d_'8852'f'45''737'_44 (coe v8) (coe v10)))
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178
                              (d_'8852'f'45''691'_50 (coe v8) (coe v10)))
                           (\ v11 v12 v13 -> coe du_ν'45'least_542 (coe v8) v12 v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.arr-≡
d_arr'45''8801'_690 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45''8801'_690 = erased
-- Once.Lang.Type.Join.fin-inj
d_fin'45'inj_696 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fin'45'inj_696 = erased
-- Once.Lang.Type.Join.<:ᶜ-antisym
d_'60''58''7580''45'antisym_702 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''7580''45'antisym_702 = erased
-- Once.Lang.Type.Join.join-unique
d_join'45'unique_742 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_join'45'unique_742 = erased
-- Once.Lang.Type.Join.complete
d_complete_754 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 -> T_Joins_84
d_complete_754 v0 v1 ~v2 ~v3 = du_complete_754 v0 v1
du_complete_754 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T_Joins_84
du_complete_754 v0 v1
  = coe du_from_766 (coe d_join'63'_582 (coe v0) (coe v1))
-- Once.Lang.Type.Join._.from
d_from_766 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T_Join'63'_154 -> T_Joins_84
d_from_766 ~v0 ~v1 ~v2 ~v3 v4 = du_from_766 v4
du_from_766 :: T_Join'63'_154 -> T_Joins_84
du_from_766 v0
  = case coe v0 of
      C_joined_162 v1 v2 -> coe v2
      C_apart_164 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.Joins-least-<:
d_Joins'45'least'45''60''58'_782 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Joins_84 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
d_Joins'45'least'45''60''58'_782 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      C_j'45'refl_88 -> coe v5
      C_j'45'void'737'_92 -> coe v6
      C_j'45'void'691'_96 -> coe v5
      C_j'45'prod_110 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v19 v20
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v25 v26
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v27 v28
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v33 v34
                                                  -> coe
                                                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62
                                                       (d_Joins'45'least'45''60''58'_782
                                                          (coe v15) (coe v17) (coe v19) (coe v27)
                                                          (coe v13) (coe v25) (coe v33))
                                                       (d_Joins'45'least'45''60''58'_782
                                                          (coe v16) (coe v18) (coe v20) (coe v28)
                                                          (coe v14) (coe v26) (coe v34))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'sum_124 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v19 v20
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72 v25 v26
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Type.C__'43'__26 v27 v28
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72 v33 v34
                                                  -> coe
                                                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72
                                                       (d_Joins'45'least'45''60''58'_782
                                                          (coe v15) (coe v17) (coe v19) (coe v27)
                                                          (coe v13) (coe v25) (coe v33))
                                                       (d_Joins'45'least'45''60''58'_782
                                                          (coe v16) (coe v18) (coe v20) (coe v28)
                                                          (coe v14) (coe v26) (coe v34))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'arr_140 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v31 v32 v33
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v34 v35 v36
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v44 v45 v46
                                                  -> coe
                                                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                       v31
                                                       (d_Joins'45'least'45''60''58'_782
                                                          (coe v17) (coe v20) (coe v23) (coe v36)
                                                          (coe v14) (coe v32) (coe v45))
                                                       (coe
                                                          du_'8852'p'45'least_28 (coe v33)
                                                          (coe v46))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'ν_148
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v10 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v15
                      -> case coe v6 of
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v19
                             -> coe
                                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84
                                  (coe du_'8852'f'45'least_60 (coe v11) (coe v15) (coe v19))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.least-<:
d_least'45''60''58'_838 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
d_least'45''60''58'_838 v0 v1 v2 v3 ~v4
  = du_least'45''60''58'_838 v0 v1 v2 v3
du_least'45''60''58'_838 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26
du_least'45''60''58'_838 v0 v1 v2 v3
  = coe
      d_Joins'45'least'45''60''58'_782 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe du_complete_754 (coe v0) (coe v1))
-- Once.Lang.Type.Join.join?-complete
d_join'63''45'complete_850 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'63''45'complete_850 v0 v1 ~v2 ~v3
  = du_join'63''45'complete_850 v0 v1
du_join'63''45'complete_850 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'63''45'complete_850 v0 v1
  = coe du_go_880 (coe d_join'63'_582 (coe v0) (coe v1))
-- Once.Lang.Type.Join._.found
d_found_870 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Joins_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_found_870 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_found_870 v5 v7
du_found_870 ::
  T_Joins_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_found_870 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Lang.Type.Join._.go
d_go_880 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_880 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_go_880 v4
du_go_880 ::
  T_Join'63'_154 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_880 v0
  = case coe v0 of
      C_joined_162 v1 v2 -> coe du_found_870 (coe v2) erased
      C_apart_164 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.join?-apart
d_join'63''45'apart_894 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'63''45'apart_894 v0 v1 ~v2 = du_join'63''45'apart_894 v0 v1
du_join'63''45'apart_894 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'63''45'apart_894 v0 v1
  = coe du_go_910 (coe d_join'63'_582 (coe v0) (coe v1)) erased
-- Once.Lang.Type.Join._.go
d_go_910 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_910 ~v0 ~v1 ~v2 v3 v4 = du_go_910 v3 v4
du_go_910 ::
  T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_910 v0 v1
  = case coe v0 of
      C_joined_162 v2 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      C_apart_164
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Join.join
d_join_920 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8
d_join_920 v0 v1
  = coe du_fromJoin'63'_934 (coe d_join'63'_582 (coe v0) (coe v1))
-- Once.Lang.Type.Join._.fromJoin?
d_fromJoin'63'_934 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Join'63'_154 -> Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8
d_fromJoin'63'_934 ~v0 ~v1 ~v2 ~v3 v4 = du_fromJoin'63'_934 v4
du_fromJoin'63'_934 ::
  T_Join'63'_154 -> Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8
du_fromJoin'63'_934 v0
  = case coe v0 of
      C_joined_162 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_apart_164 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
