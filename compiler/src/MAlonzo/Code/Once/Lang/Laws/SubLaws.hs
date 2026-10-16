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

module MAlonzo.Code.Once.Lang.Laws.SubLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub

-- Once.Lang.Laws.SubLaws.⊑π-unique
d_'8849'π'45'unique_16 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'unique_16 = erased
-- Once.Lang.Laws.SubLaws.⊑π-trans
d_'8849'π'45'trans_24 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8849'π'45'trans_24 ~v0 ~v1 ~v2 v3 v4
  = du_'8849'π'45'trans_24 v3 v4
du_'8849'π'45'trans_24 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
du_'8849'π'45'trans_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.SubLaws.<:-unique
d_'60''58''45'unique_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'unique_34 = erased
-- Once.Lang.Laws.SubLaws.<:-trans
d_'60''58''45'trans_86 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'60''58''45'trans_86 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
        -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36 -> coe v4
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38 -> coe v4
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40 -> coe v4
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v12 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v28 v29 v30
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v31 v32 v33
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56
                                         (d_'60''58''45'trans_86
                                            (coe v31) (coe v18) (coe v15) (coe v28) (coe v12))
                                         (d_'60''58''45'trans_86
                                            (coe v17) (coe v20) (coe v33) (coe v13) (coe v29))
                                         (coe du_'8849'π'45'trans_24 (coe v14) (coe v30))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66
                                         (d_'60''58''45'trans_86
                                            (coe v11) (coe v13) (coe v21) (coe v9) (coe v19))
                                         (d_'60''58''45'trans_86
                                            (coe v12) (coe v14) (coe v22) (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76
                                         (d_'60''58''45'trans_86
                                            (coe v11) (coe v13) (coe v21) (coe v9) (coe v19))
                                         (d_'60''58''45'trans_86
                                            (coe v12) (coe v14) (coe v22) (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80 -> coe v4
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v8
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v12
               -> coe
                    MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88
                    (coe du_'8849'π'45'trans_24 (coe v8) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_94 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
