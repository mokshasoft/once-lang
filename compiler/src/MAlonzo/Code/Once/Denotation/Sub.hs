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
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Denotation.Sub.fmapT-id
d_fmapT'45'id_12 ::
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45'id_12 = erased
-- Once.Denotation.Sub.fmapT-∘
d_fmapT'45''8728'_32 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45''8728'_32 = erased
-- Once.Denotation.Sub.fmapT-cong
d_fmapT'45'cong_54 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45'cong_54 = erased
-- Once.Denotation.Sub.⟦_⟧<:
d_'10214'_'10215''60''58'_66 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 -> AgdaAny -> AgdaAny
d_'10214'_'10215''60''58'_66 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                                              (coe
                                                 d_'10214'_'10215''60''58'_66 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe v3 v22))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                                              (coe
                                                 d_'10214'_'10215''60''58'_66 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe
                                                 v3
                                                 (d_'10214'_'10215''60''58'_66
                                                    (coe v19) (coe v14) (coe v11) (coe v22))))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                                              (coe
                                                 d_'10214'_'10215''60''58'_66 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe
                                                 v3
                                                 (d_'10214'_'10215''60''58'_66
                                                    (coe v19) (coe v14) (coe v11) (coe v22))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_'10214'_'10215''60''58'_66 (coe v10) (coe v12) (coe v8)
                                     (coe v14))
                                  (coe
                                     d_'10214'_'10215''60''58'_66 (coe v11) (coe v13) (coe v9)
                                     (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_'10214'_'10215''60''58'_66 (coe v10) (coe v12) (coe v8)
                                     (coe v14))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_'10214'_'10215''60''58'_66 (coe v11) (coe v13) (coe v9)
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Sub.<:-refl-id
d_'60''58''45'refl'45'id_130 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'refl'45'id_130 = erased
-- Once.Denotation.Sub.<:-trans-∘
d_'60''58''45'trans'45''8728'_216 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'trans'45''8728'_216 = erased
-- Once.Denotation.Sub.void-middle
d_void'45'middle_326 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_void'45'middle_326 = erased
