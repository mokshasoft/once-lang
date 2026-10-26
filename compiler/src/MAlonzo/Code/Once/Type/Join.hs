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

module MAlonzo.Code.Once.Type.Join where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Grade
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Join.⊔p-ˡ
d_'8852'p'45''737'_10 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45''737'_10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> coe
                           seq (coe v3) (coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58)
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.⊔p-ʳ
d_'8852'p'45''691'_16 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45''691'_16 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_12 (coe v1)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
                    MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.⊔p-least
d_'8852'p'45'least_26 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45'least_26 ~v0 ~v1 ~v2 v3 v4
  = du_'8852'p'45'least_26 v3 v4
du_'8852'p'45'least_26 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
du_'8852'p'45'least_26 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join._⊔f_
d__'8852'f__34 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34
d__'8852'f__34 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.⊔f-ˡ
d_'8852'f'45''737'_42 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'f'45''737'_42 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.⊔f-ʳ
d_'8852'f'45''691'_48 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'f'45''691'_48 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> coe
             MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_12
             (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v1))
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.⊔f-least
d_'8852'f'45'least_58 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'f'45'least_58 v0 ~v1 ~v2 v3 v4
  = du_'8852'f'45'least_58 v0 v3 v4
du_'8852'f'45'least_58 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
du_'8852'f'45'least_58 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v2
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.shape
d_shape_66 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_shape_66 ~v0 v1 = du_shape_66 v1
du_shape_66 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_shape_66 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1 -> coe (9 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2 -> coe (3 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe (4 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1 -> coe (5 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2 -> coe (6 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (7 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.<:ᶜ-shape
d_'60''58''7580''45'shape_74 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''7580''45'shape_74 = erased
-- Once.Type.Join.UB
d_UB_80 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_UB_80 = erased
-- Once.Type.Join.Joins
d_Joins_90 a0 a1 a2 a3 = ()
data T_Joins_90
  = C_j'45'refl_96 | C_j'45'void'737'_100 | C_j'45'void'691'_104 |
    C_j'45'prod_118 T_Joins_90 T_Joins_90 |
    C_j'45'sum_132 T_Joins_90 T_Joins_90 | C_j'45'arr_148 T_Joins_90 |
    C_j'45'ν_156
-- Once.Type.Join.Join?
d_Join'63'_164 a0 a1 a2 = ()
data T_Join'63'_164
  = C_joined_174 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Joins_90 |
    C_apart_176
-- Once.Type.Join.reflJ
d_reflJ_182 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
d_reflJ_182 ~v0 v1 = du_reflJ_182 v1
du_reflJ_182 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
du_reflJ_182 v0
  = coe
      MAlonzo.Code.Once.Spec.Sub.C_constructor_174
      (coe
         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''45'refl_84 (coe v0))
      (coe
         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''45'refl_84 (coe v0))
      (coe (\ v1 v2 v3 -> v2))
-- Once.Type.Join.voidˡ
d_void'737'_194 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
d_void'737'_194 ~v0 v1 = du_void'737'_194 v1
du_void'737'_194 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
du_void'737'_194 v0
  = coe
      MAlonzo.Code.Once.Spec.Sub.C_constructor_174
      (coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'void_82)
      (coe
         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''45'refl_84 (coe v0))
      (coe (\ v1 v2 v3 -> v3))
-- Once.Type.Join.voidʳ
d_void'691'_206 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
d_void'691'_206 ~v0 v1 = du_void'691'_206 v1
du_void'691'_206 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
du_void'691'_206 v0
  = coe
      MAlonzo.Code.Once.Spec.Sub.C_constructor_174
      (coe
         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''45'refl_84 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'void_82)
      (coe (\ v1 v2 v3 -> v2))
-- Once.Type.Join.clashJ
d_clashJ_220 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
d_clashJ_220 ~v0 v1 v2 ~v3 v4 v5 = du_clashJ_220 v1 v2 v4 v5
du_clashJ_220 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
du_clashJ_220 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5) (coe C_joined_174 (coe v1) (coe C_j'45'void'737'_100))
             else coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe C_joined_174 (coe v0) (coe C_j'45'void'691'_104))
                              else coe seq (coe v7) (coe C_apart_176)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.prod-least
d_prod'45'least_254 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
d_prod'45'least_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_prod'45'least_254 v7 v8 v9 v10 v11
du_prod'45'least_254 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
du_prod'45'least_254 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116
                           (coe MAlonzo.Code.Once.Spec.Sub.d_least_172 v1 v11 v9 v17)
                           (coe MAlonzo.Code.Once.Spec.Sub.d_least_172 v2 v12 v10 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.prod-fst
d_prod'45'fst_278 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prod'45'fst_278 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_prod'45'fst_278 v5
du_prod'45'fst_278 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prod'45'fst_278 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v17 v18
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
-- Once.Type.Join.prod-snd
d_prod'45'snd_294 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prod'45'snd_294 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_prod'45'snd_294 v5
du_prod'45'snd_294 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prod'45'snd_294 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v17 v18
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
-- Once.Type.Join.prodJ
d_prodJ_310 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Join'63'_164 -> T_Join'63'_164 -> T_Join'63'_164
d_prodJ_310 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_prodJ_310 v5 v6
du_prodJ_310 :: T_Join'63'_164 -> T_Join'63'_164 -> T_Join'63'_164
du_prodJ_310 v0 v1
  = case coe v0 of
      C_joined_174 v2 v3
        -> case coe v1 of
             C_joined_174 v4 v5
               -> coe
                    C_joined_174
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v2) (coe v4))
                    (coe C_j'45'prod_118 v3 v5)
             C_apart_176 -> coe C_apart_176
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apart_176 -> coe C_apart_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.sum-least
d_sum'45'least_344 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
d_sum'45'least_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_sum'45'least_344 v7 v8 v9 v10 v11
du_sum'45'least_344 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
du_sum'45'least_344 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126
                           (coe MAlonzo.Code.Once.Spec.Sub.d_least_172 v1 v11 v9 v17)
                           (coe MAlonzo.Code.Once.Spec.Sub.d_least_172 v2 v12 v10 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.sum-inl
d_sum'45'inl_368 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sum'45'inl_368 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sum'45'inl_368 v5
du_sum'45'inl_368 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sum'45'inl_368 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v17 v18
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
-- Once.Type.Join.sum-inr
d_sum'45'inr_384 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sum'45'inr_384 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sum'45'inr_384 v5
du_sum'45'inr_384 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sum'45'inr_384 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v9 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v17 v18
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
-- Once.Type.Join.sumJ
d_sumJ_400 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Join'63'_164 -> T_Join'63'_164 -> T_Join'63'_164
d_sumJ_400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sumJ_400 v5 v6
du_sumJ_400 :: T_Join'63'_164 -> T_Join'63'_164 -> T_Join'63'_164
du_sumJ_400 v0 v1
  = case coe v0 of
      C_joined_174 v2 v3
        -> case coe v1 of
             C_joined_174 v4 v5
               -> coe
                    C_joined_174
                    (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v2) (coe v4))
                    (coe C_j'45'sum_132 v3 v5)
             C_apart_176 -> coe C_apart_176
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apart_176 -> coe C_apart_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.arr-least
d_arr'45'least_436 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
d_arr'45'least_436 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_arr'45'least_436 v5 v9 v10 v11
du_arr'45'least_436 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
du_arr'45'least_436 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106
                           (coe MAlonzo.Code.Once.Spec.Sub.d_least_172 v1 v14 v10 v21)
                           (coe du_'8852'p'45'least_26 (coe v11) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.arr-cod
d_arr'45'cod_462 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arr'45'cod_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_arr'45'cod_462 v7
du_arr'45'cod_462 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arr'45'cod_462 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v11 v12
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v22 v23
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
-- Once.Type.Join.arr-dom
d_arr'45'dom_482 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45'dom_482 = erased
-- Once.Type.Join.arr-q
d_arr'45'q_502 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45'q_502 = erased
-- Once.Type.Join.arrJ
d_arrJ_522 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164 -> T_Join'63'_164
d_arrJ_522 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_arrJ_522 v1 v5 v7 v8 v9 v10 v11
du_arrJ_522 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164 -> T_Join'63'_164
du_arrJ_522 v0 v1 v2 v3 v4 v5 v6
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
                                        C_joined_174 v11 v12
                                          -> coe
                                               C_joined_174
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                  (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.Grade.d__'8852'p__24
                                                        (coe v2) (coe v3)))
                                                  (coe v11))
                                               (coe C_j'45'arr_148 v12)
                                        C_apart_176 -> coe C_apart_176
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe seq (coe v10) (coe C_apart_176)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v8) (coe C_apart_176)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.eqJ
d_eqJ_554 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  ((MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Join'63'_164
d_eqJ_554 ~v0 v1 ~v2 v3 ~v4 = du_eqJ_554 v1 v3
du_eqJ_554 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
du_eqJ_554 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe C_joined_174 (coe v0) (coe C_j'45'refl_96))
             else coe seq (coe v3) (coe C_apart_176)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.μ-apart
d_μ'45'apart_568 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_μ'45'apart_568 = erased
-- Once.Type.Join.var-apart
d_var'45'apart_578 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_var'45'apart_578 = erased
-- Once.Type.Join.ν-least
d_ν'45'least_592 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
d_ν'45'least_592 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_ν'45'least_592 v3 v5 v6
du_ν'45'least_592 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
du_ν'45'least_592 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138 v10
               -> coe
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138
                    (coe du_'8852'f'45'least_58 (coe v0) (coe v6) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.ν-apart
d_ν'45'apart_608 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ν'45'apart_608 = erased
-- Once.Type.Join.νJ
d_νJ_622 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
d_νJ_622 ~v0 v1 ~v2 v3 v4 v5 = du_νJ_622 v1 v3 v4 v5
du_νJ_622 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
du_νJ_622 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       C_joined_174
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v0)
                          (coe d__'8852'f__34 (coe v1) (coe v2)))
                       (coe C_j'45'ν_156))
             else coe seq (coe v5) (coe C_apart_176)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.join?
d_join'63'_638 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_Join'63'_164
d_join'63'_638 v0 v1 v2
  = coe
      d_joinS_646 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe du_shape_66 (coe v1)) (coe du_shape_66 (coe v2)))
-- Once.Type.Join.joinS
d_joinS_646 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Join'63'_164
d_joinS_646 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C_var_16 v6
                      -> coe
                           seq (coe v5)
                           (coe
                              seq (coe v2)
                              (coe
                                 du_eqJ_554 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe v0) (coe v1)
                                    (coe v2))))
                    MAlonzo.Code.Once.Spec.Type.C_Unit_18
                      -> coe
                           seq (coe v5)
                           (coe seq (coe v2) (coe C_joined_174 (coe v1) (coe C_j'45'refl_96)))
                    MAlonzo.Code.Once.Spec.Type.C_Void_20
                      -> coe
                           seq (coe v5)
                           (coe seq (coe v2) (coe C_joined_174 (coe v1) (coe C_j'45'refl_96)))
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
                      -> coe
                           seq (coe v5)
                           (case coe v2 of
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
                                -> coe
                                     du_prodJ_310 (coe d_join'63'_638 (coe v0) (coe v6) (coe v8))
                                     (coe d_join'63'_638 (coe v0) (coe v7) (coe v9))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
                      -> coe
                           seq (coe v5)
                           (case coe v2 of
                              MAlonzo.Code.Once.Spec.Type.C__'43'__24 v8 v9
                                -> coe
                                     du_sumJ_400 (coe d_join'63'_638 (coe v0) (coe v6) (coe v8))
                                     (coe d_join'63'_638 (coe v0) (coe v7) (coe v9))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
                      -> case coe v7 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                             -> coe
                                  seq (coe v5)
                                  (case coe v2 of
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
                                       -> case coe v12 of
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                                              -> coe
                                                   du_arrJ_522 (coe v6) (coe v9) (coe v10) (coe v15)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                      (coe v0) (coe v6) (coe v11))
                                                   (coe
                                                      MAlonzo.Code.Once.Type.DecEq.d__'8799'q__6
                                                      (coe v9) (coe v14))
                                                   (coe d_join'63'_638 (coe v0) (coe v8) (coe v13))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
                      -> coe
                           seq (coe v5)
                           (coe
                              seq (coe v2)
                              (coe
                                 du_eqJ_554 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe v0) (coe v1)
                                    (coe v2))))
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
                      -> coe
                           seq (coe v5)
                           (case coe v2 of
                              MAlonzo.Code.Once.Spec.Type.C_ν_30 v8 v9
                                -> coe
                                     du_νJ_622 (coe v6) (coe v7) (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Type.DecEq.d__'8799'F__224 (coe v0)
                                        (coe v6) (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Type.C_Int_32
                      -> coe
                           seq (coe v5)
                           (coe seq (coe v2) (coe C_joined_174 (coe v1) (coe C_j'45'refl_96)))
                    MAlonzo.Code.Once.Spec.Type.C_Float_34
                      -> coe
                           seq (coe v5)
                           (coe seq (coe v2) (coe C_joined_174 (coe v1) (coe C_j'45'refl_96)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v5)
                    (coe
                       du_clashJ_220 (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Void_20))
                       (coe
                          MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe v0) (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.sound
d_sound_714 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Joins_90 -> MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
d_sound_714 ~v0 v1 v2 v3 v4 = du_sound_714 v1 v2 v3 v4
du_sound_714 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Joins_90 -> MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148
du_sound_714 v0 v1 v2 v3
  = case coe v3 of
      C_j'45'refl_96 -> coe du_reflJ_182 (coe v0)
      C_j'45'void'737'_100 -> coe du_void'737'_194 (coe v1)
      C_j'45'void'691'_104 -> coe du_void'691'_206 (coe v0)
      C_j'45'prod_118 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Spec.Sub.C_constructor_174
                                  (coe
                                     MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116
                                     (MAlonzo.Code.Once.Spec.Sub.d_left_166
                                        (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Spec.Sub.d_left_166
                                        (coe du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116
                                     (MAlonzo.Code.Once.Spec.Sub.d_right_168
                                        (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Spec.Sub.d_right_168
                                        (coe du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          du_prod'45'least_254 (coe v18)
                                          (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10))
                                          (coe
                                             du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'sum_132 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Spec.Sub.C_constructor_174
                                  (coe
                                     MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126
                                     (MAlonzo.Code.Once.Spec.Sub.d_left_166
                                        (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Spec.Sub.d_left_166
                                        (coe du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126
                                     (MAlonzo.Code.Once.Spec.Sub.d_right_168
                                        (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10)))
                                     (MAlonzo.Code.Once.Spec.Sub.d_right_168
                                        (coe du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          du_sum'45'least_344 (coe v18)
                                          (coe du_sound_714 (coe v12) (coe v14) (coe v16) (coe v10))
                                          (coe
                                             du_sound_714 (coe v13) (coe v15) (coe v17) (coe v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'arr_148 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                                    -> case coe v2 of
                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v22 v23 v24
                                           -> coe
                                                MAlonzo.Code.Once.Spec.Sub.C_constructor_174
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106
                                                   (MAlonzo.Code.Once.Spec.Sub.d_left_166
                                                      (coe
                                                         du_sound_714 (coe v14) (coe v19) (coe v24)
                                                         (coe v11)))
                                                   (d_'8852'p'45''737'_10 (coe v16) (coe v21)))
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106
                                                   (MAlonzo.Code.Once.Spec.Sub.d_right_168
                                                      (coe
                                                         du_sound_714 (coe v14) (coe v19) (coe v24)
                                                         (coe v11)))
                                                   (d_'8852'p'45''691'_16 (coe v16) (coe v21)))
                                                (coe
                                                   (\ v25 ->
                                                      coe
                                                        du_arr'45'least_436 (coe v25)
                                                        (coe
                                                           du_sound_714 (coe v14) (coe v19)
                                                           (coe v24) (coe v11))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'ν_156
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_constructor_174
                           (coe
                              MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138
                              (d_'8852'f'45''737'_42 (coe v8) (coe v10)))
                           (coe
                              MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138
                              (d_'8852'f'45''691'_48 (coe v8) (coe v10)))
                           (coe (\ v11 -> coe du_ν'45'least_592 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.arr-≡
d_arr'45''8801'_748 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'45''8801'_748 = erased
-- Once.Type.Join.fin-inj
d_fin'45'inj_754 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fin'45'inj_754 = erased
-- Once.Type.Join.<:ᶜ-antisym
d_'60''58''7580''45'antisym_762 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''7580''45'antisym_762 = erased
-- Once.Type.Join.join-unique
d_join'45'unique_804 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_join'45'unique_804 = erased
-- Once.Type.Join.complete
d_complete_818 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 -> T_Joins_90
d_complete_818 v0 v1 v2 ~v3 ~v4 = du_complete_818 v0 v1 v2
du_complete_818 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_Joins_90
du_complete_818 v0 v1 v2
  = coe du_from_830 (coe d_join'63'_638 (coe v0) (coe v1) (coe v2))
-- Once.Type.Join._.from
d_from_830 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  T_Join'63'_164 -> T_Joins_90
d_from_830 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_from_830 v5
du_from_830 :: T_Join'63'_164 -> T_Joins_90
du_from_830 v0
  = case coe v0 of
      C_joined_174 v1 v2 -> coe v2
      C_apart_176 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.Joins-least-<:
d_Joins'45'least'45''60''58'_848 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Joins_90 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_Joins'45'least'45''60''58'_848 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_Joins'45'least'45''60''58'_848 v1 v2 v3 v4 v5 v6 v7
du_Joins'45'least'45''60''58'_848 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Joins_90 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
du_Joins'45'least'45''60''58'_848 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      C_j'45'refl_96 -> coe v5
      C_j'45'void'737'_100 -> coe v6
      C_j'45'void'691'_104 -> coe v5
      C_j'45'prod_118 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v19 v20
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v25 v26
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v27 v28
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v33 v34
                                                  -> coe
                                                       MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50
                                                       (coe
                                                          du_Joins'45'least'45''60''58'_848
                                                          (coe v15) (coe v17) (coe v19) (coe v27)
                                                          (coe v13) (coe v25) (coe v33))
                                                       (coe
                                                          du_Joins'45'least'45''60''58'_848
                                                          (coe v16) (coe v18) (coe v20) (coe v28)
                                                          (coe v14) (coe v26) (coe v34))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'sum_132 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v19 v20
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v25 v26
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v27 v28
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v33 v34
                                                  -> coe
                                                       MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60
                                                       (coe
                                                          du_Joins'45'least'45''60''58'_848
                                                          (coe v15) (coe v17) (coe v19) (coe v27)
                                                          (coe v13) (coe v25) (coe v33))
                                                       (coe
                                                          du_Joins'45'least'45''60''58'_848
                                                          (coe v16) (coe v18) (coe v20) (coe v28)
                                                          (coe v14) (coe v26) (coe v34))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'arr_148 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v21 v22 v23
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v31 v32 v33
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v34 v35 v36
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v44 v45 v46
                                                  -> coe
                                                       MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                                       v31
                                                       (coe
                                                          du_Joins'45'least'45''60''58'_848
                                                          (coe v17) (coe v20) (coe v23) (coe v36)
                                                          (coe v14) (coe v32) (coe v45))
                                                       (coe
                                                          du_'8852'p'45'least_26 (coe v33)
                                                          (coe v46))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_j'45'ν_156
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v15
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v19
                             -> coe
                                  MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72
                                  (coe du_'8852'f'45'least_58 (coe v11) (coe v15) (coe v19))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.least-<:
d_least'45''60''58'_906 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_least'45''60''58'_906 v0 v1 v2 v3 v4 ~v5
  = du_least'45''60''58'_906 v0 v1 v2 v3 v4
du_least'45''60''58'_906 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
du_least'45''60''58'_906 v0 v1 v2 v3 v4
  = coe
      du_Joins'45'least'45''60''58'_848 (coe v1) (coe v2) (coe v3)
      (coe v4) (coe du_complete_818 (coe v0) (coe v1) (coe v2))
-- Once.Type.Join.join?-complete
d_join'63''45'complete_920 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'63''45'complete_920 v0 v1 v2 ~v3 ~v4
  = du_join'63''45'complete_920 v0 v1 v2
du_join'63''45'complete_920 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'63''45'complete_920 v0 v1 v2
  = coe du_go_950 (coe d_join'63'_638 (coe v0) (coe v1) (coe v2))
-- Once.Type.Join._.found
d_found_940 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Joins_90 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_found_940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 = du_found_940 v6 v8
du_found_940 ::
  T_Joins_90 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_found_940 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Type.Join._.go
d_go_950 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 ->
  T_Join'63'_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_950 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_go_950 v5
du_go_950 ::
  T_Join'63'_164 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_950 v0
  = case coe v0 of
      C_joined_174 v1 v2 -> coe du_found_940 (coe v2) erased
      C_apart_176 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.join?-apart
d_join'63''45'apart_966 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'63''45'apart_966 v0 v1 v2 ~v3
  = du_join'63''45'apart_966 v0 v1 v2
du_join'63''45'apart_966 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'63''45'apart_966 v0 v1 v2
  = coe
      du_go_982 (coe d_join'63'_638 (coe v0) (coe v1) (coe v2)) erased
-- Once.Type.Join._.go
d_go_982 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Join'63'_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_982 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_go_982 v4 v5
du_go_982 ::
  T_Join'63'_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_982 v0 v1
  = case coe v0 of
      C_joined_174 v2 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      C_apart_176
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Join.join
d_join_994 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_join_994 v0 v1 v2
  = coe
      du_fromJoin'63'_1008
      (coe d_join'63'_638 (coe v0) (coe v1) (coe v2))
-- Once.Type.Join._.fromJoin?
d_fromJoin'63'_1008 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Join'63'_164 -> Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_fromJoin'63'_1008 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_fromJoin'63'_1008 v5
du_fromJoin'63'_1008 ::
  T_Join'63'_164 -> Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_fromJoin'63'_1008 v0
  = case coe v0 of
      C_joined_174 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_apart_176 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
