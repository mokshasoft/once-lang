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

module MAlonzo.Code.Once.Denotation.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub

-- Once.Denotation.Sub.⟦_⟧<:
d_'10214'_'10215''60''58'_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215''60''58'_10 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe
                                                 d_'10214'_'10215''60''58'_10 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe v3 v22))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe
                                                 d_'10214'_'10215''60''58'_10 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe
                                                 v3
                                                 (d_'10214'_'10215''60''58'_10
                                                    (coe v19) (coe v14) (coe v11) (coe v22))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe
                                                 d_'10214'_'10215''60''58'_10 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe
                                                 v3
                                                 (d_'10214'_'10215''60''58'_10
                                                    (coe v19) (coe v14) (coe v11) (coe v22))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_'10214'_'10215''60''58'_10 (coe v10) (coe v12) (coe v8)
                                     (coe v14))
                                  (coe
                                     d_'10214'_'10215''60''58'_10 (coe v11) (coe v13) (coe v9)
                                     (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_'10214'_'10215''60''58'_10 (coe v10) (coe v12) (coe v8)
                                     (coe v14))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_'10214'_'10215''60''58'_10 (coe v11) (coe v13) (coe v9)
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Sub.<:-refl-id
d_'60''58''45'refl'45'id_70 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'refl'45'id_70 = erased
-- Once.Denotation.Sub.<:-trans-∘
d_'60''58''45'trans'45''8728'_152 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'trans'45''8728'_152 = erased
