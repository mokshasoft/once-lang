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

module MAlonzo.Code.Once.Internal.Laws.SubLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Laws.SubLaws.⊑π-unique
d_'8849'π'45'unique_16 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'unique_16 = erased
-- Once.Internal.Laws.SubLaws.⊑π-trans
d_'8849'π'45'trans_24 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8849'π'45'trans_24 ~v0 ~v1 ~v2 v3 v4
  = du_'8849'π'45'trans_24 v3 v4
du_'8849'π'45'trans_24 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
du_'8849'π'45'trans_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.SubLaws.<:-unique
d_'60''58''45'unique_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'unique_36 = erased
-- Once.Internal.Laws.SubLaws.<:-trans
d_'60''58''45'trans_90 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_'60''58''45'trans_90 ~v0 v1 v2 v3 v4 v5
  = du_'60''58''45'trans_90 v1 v2 v3 v4 v5
du_'60''58''45'trans_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
du_'60''58''45'trans_90 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18 -> coe v4
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20 -> coe v4
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22 -> coe v4
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24 -> coe v4
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v12 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v28 v29 v30
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v31 v32 v33
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                         (coe
                                            du_'60''58''45'trans_90 (coe v31) (coe v18) (coe v15)
                                            (coe v28) (coe v12))
                                         (coe
                                            du_'60''58''45'trans_90 (coe v17) (coe v20) (coe v33)
                                            (coe v13) (coe v29))
                                         (coe du_'8849'π'45'trans_24 (coe v14) (coe v30))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Spec.Type.C__'42'__22 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50
                                         (coe
                                            du_'60''58''45'trans_90 (coe v11) (coe v13) (coe v21)
                                            (coe v9) (coe v19))
                                         (coe
                                            du_'60''58''45'trans_90 (coe v12) (coe v14) (coe v22)
                                            (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v19 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Spec.Type.C__'43'__24 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60
                                         (coe
                                            du_'60''58''45'trans_90 (coe v11) (coe v13) (coe v21)
                                            (coe v9) (coe v19))
                                         (coe
                                            du_'60''58''45'trans_90 (coe v12) (coe v14) (coe v22)
                                            (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64 -> coe v4
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v8
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v12
               -> coe
                    MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72
                    (coe du_'8849'π'45'trans_24 (coe v8) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
