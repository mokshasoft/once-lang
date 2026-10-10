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

module MAlonzo.Code.Once.Type.SubLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Type.SubLaws.⊑π-unique
d_'8849'π'45'unique_14 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'unique_14 = erased
-- Once.Type.SubLaws.⊑π-refl
d_'8849'π'45'refl_18 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
d_'8849'π'45'refl_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe MAlonzo.Code.Once.Type.Sub.C_'8849''45'pure_8
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe MAlonzo.Code.Once.Type.Sub.C_'8849''45'eff_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.SubLaws.⊑π-trans
d_'8849'π'45'trans_26 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
d_'8849'π'45'trans_26 ~v0 ~v1 ~v2 v3 v4
  = du_'8849'π'45'trans_26 v3 v4
du_'8849'π'45'trans_26 ::
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
du_'8849'π'45'trans_26 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'pure_8 -> coe v1
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'eff_10
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'pe_12
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.SubLaws.<:-unique
d_'60''58''45'unique_38 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'unique_38 = erased
-- Once.Type.SubLaws.<:-refl
d_'60''58''45'refl_86 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24
d_'60''58''45'refl_86 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_30
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_28
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_60
             (d_'60''58''45'refl_86 (coe v1)) (d_'60''58''45'refl_86 (coe v2))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_70
             (d_'60''58''45'refl_86 (coe v1)) (d_'60''58''45'refl_86 (coe v2))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> coe
                    MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_50
                    (d_'60''58''45'refl_86 (coe v1)) (d_'60''58''45'refl_86 (coe v3))
                    (d_'8849'π'45'refl_18 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_74
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_82
             (d_'8849'π'45'refl_18 (coe v2))
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_32
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_34
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_88
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.SubLaws.<:-trans
d_'60''58''45'trans_116 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__24
d_'60''58''45'trans_116 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'void_28
        -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_28
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_30 -> coe v4
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_32 -> coe v4
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_34 -> coe v4
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_50 v12 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_50 v28 v29 v30
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v31 v32 v33
                                    -> coe
                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_50
                                         (d_'60''58''45'trans_116
                                            (coe v31) (coe v18) (coe v15) (coe v28) (coe v12))
                                         (d_'60''58''45'trans_116
                                            (coe v17) (coe v20) (coe v33) (coe v13) (coe v29))
                                         (coe du_'8849'π'45'trans_26 (coe v14) (coe v30))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_60 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_60 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'42'__124 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_60
                                         (d_'60''58''45'trans_116
                                            (coe v11) (coe v13) (coe v21) (coe v9) (coe v19))
                                         (d_'60''58''45'trans_116
                                            (coe v12) (coe v14) (coe v22) (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_70 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_70 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_70
                                         (d_'60''58''45'trans_116
                                            (coe v11) (coe v13) (coe v21) (coe v9) (coe v19))
                                         (d_'60''58''45'trans_116
                                            (coe v12) (coe v14) (coe v22) (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_74 -> coe v4
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_82 v8
        -> case coe v4 of
             MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_82 v12
               -> coe
                    MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_82
                    (coe du_'8849'π'45'trans_26 (coe v8) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_88 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
