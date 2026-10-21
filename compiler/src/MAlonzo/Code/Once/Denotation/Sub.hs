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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Denotation.Sub.⟦_⟧<:
d_'10214'_'10215''60''58'_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215''60''58'_10 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18 -> coe v3
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20 -> coe v3
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22 -> coe v3
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                                              (coe
                                                 d_'10214'_'10215''60''58'_10 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe v3 v22))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                                              (coe
                                                 d_'10214'_'10215''60''58'_10 (coe v16) (coe v21)
                                                 (coe v12))
                                              (coe
                                                 v3
                                                 (d_'10214'_'10215''60''58'_10
                                                    (coe v19) (coe v14) (coe v11) (coe v22))))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
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
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v12 v13
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
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v12 v13
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
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62 -> coe v3
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Sub.<:-refl-rel
d_'60''58''45'refl'45'rel_72 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''58''45'refl'45'rel_72 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20 -> coe (\ v3 -> v3)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           (\ v9 ->
                              case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe d_'60''58''45'refl'45'rel_72 v3 v5 v7 v10)
                                       (coe d_'60''58''45'refl'45'rel_72 v4 v6 v8 v11)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                      -> coe (\ v7 -> coe d_'60''58''45'refl'45'rel_72 v3 v5 v6 v7)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                      -> coe (\ v7 -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                      -> coe (\ v7 -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                      -> coe (\ v7 -> coe d_'60''58''45'refl'45'rel_72 v4 v5 v6 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           (\ v8 ->
                              coe
                                MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                (coe
                                   d_'10214'_'10215''60''58'_10 (coe v5) (coe v5)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                      (coe v5)))
                                (coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                (coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) (coe v8)
                                (coe d_'60''58''45'refl'45'rel_72 (coe v5)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           (\ v8 v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                (coe
                                   d_'10214'_'10215''60''58'_10 (coe v5) (coe v5)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                      (coe v5)))
                                (coe
                                   v1
                                   (d_'10214'_'10215''60''58'_10
                                      (coe v3) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                         (coe v3))
                                      (coe v9)))
                                (coe v2 v10)
                                (coe
                                   v8
                                   (d_'10214'_'10215''60''58'_10
                                      (coe v3) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                         (coe v3))
                                      (coe v9))
                                   v10 (coe d_'60''58''45'refl'45'rel_72 v3 v9 v10 v11))
                                (coe d_'60''58''45'refl'45'rel_72 (coe v5)))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           (\ v8 v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                (coe
                                   d_'10214'_'10215''60''58'_10 (coe v5) (coe v5)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                      (coe v5)))
                                (coe
                                   v1
                                   (d_'10214'_'10215''60''58'_10
                                      (coe v3) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                         (coe v3))
                                      (coe v9)))
                                (coe v2 v10)
                                (coe
                                   v8
                                   (d_'10214'_'10215''60''58'_10
                                      (coe v3) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                         (coe v3))
                                      (coe v9))
                                   v10 (coe d_'60''58''45'refl'45'rel_72 v3 v9 v10 v11))
                                (coe d_'60''58''45'refl'45'rel_72 (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe (\ v4 -> v4)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe (\ v5 -> v5)
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> coe (\ v3 -> v3)
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> coe (\ v3 -> v3)
      _ -> MAlonzo.RTE.mazUnreachableError
